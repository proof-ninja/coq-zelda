Require Import List PeanoNat.
Import ListNotations.
Require Import Common Dict Eq.

Definition Treasures := nat.

Definition RoomId := nat.
Definition RoomIdDec := nat_eqDec.

Record Room := {
    id : RoomId;
    goal : bool;
    treasures: Treasures;
    doors: list (bool * RoomId);
}.

Record State := {
    table: Dict.t RoomIdDec Room;
    keys : nat;
    pos : RoomId;
}.


Definition free_doors room :=
  List.filter (fun '(locked, _) => negb locked) (doors room).
Definition locked_doors room :=
  List.filter (fun '(locked, _) => locked) (doors room).

Parameter error_room : Room.
Definition find_room state id := Dict.find_err state.(table) error_room id.
Definition current_room state := find_room state state.(pos).

Definition FreeRoomOf room1 room2_id : Prop:=
  In (false, room2_id) (doors room1).

Definition LockedRoomOf room1 room2_id :=
  In (true,  room2_id) (doors room1).

Definition room_set_treasures treasures room :=
  {| treasures:=treasures; goal:=room.(goal); id:=room.(id); doors:=room.(doors); |}.
Definition room_unlock_door (room_id : RoomId) room :=
  {| treasures:=room.(treasures); goal:=room.(goal); id:=room.(id);
     doors := List.map (fun '(locked, id) => if id =? room_id then (false, id) else (locked, id)) room.(doors);
  |}.

Definition enter_free state room2_id : State :=
  let room2 := find_room state room2_id in
  {|
    keys := state.(keys) + room2.(treasures);
    pos := room2.(id);
    table :=
      Dict.update _ room2.(id) (room_set_treasures 0 room2) state.(table);
  |}.

Definition enter_locked state room2_id : State :=
  let room1' := room_unlock_door room2_id (current_room state) in
  let room2 := find_room state room2_id in
  let room2' := room_set_treasures 0 room2
                  |> room_unlock_door state.(pos)
  in
  {|
    keys := state.(keys) + room2.(treasures) - 1;
    pos := room2.(id);
    table :=
      state.(table)
      |> Dict.update _ room2_id room2'
      |> Dict.update _ state.(pos) room1'
  |}.

Axiom id_find_room : forall i state,
  id (find_room state i) = i.

Lemma goal_enter_free id state room2 :
  (find_room (enter_free state room2) id).(goal) = (find_room state id).(goal).
Proof.
  unfold find_room, enter_free. simpl.
  destruct (room2 =? id).
  - now rewrite id_find_room, e, find_err_update_eq.
  - now rewrite id_find_room, find_err_update_neq.
Qed.

Lemma pos_enter_free state room2 :
  (enter_free state room2).(pos) = room2.
Proof.
  unfold enter_free. now rewrite id_find_room.
Qed.
Lemma keys_enter_free state room2 :
  (enter_free state room2).(keys) = state.(keys) + (find_room state room2).(treasures).
Proof. now unfold enter_free. Qed.
Lemma doors_enter_free id state room2 :
  (find_room (enter_free state  room2) id).(doors) = (find_room state id).(doors).
Proof.
  unfold enter_free, find_room at 1. simpl.
  rewrite id_find_room.
  destruct (room2 =? id).
  - rewrite e, find_err_update_eq.
    now unfold room_set_treasures.
  - now rewrite find_err_update_neq.
Qed.

Lemma pos_enter_locked state room2 :
  (enter_locked state room2).(pos) = room2.
Proof.
  unfold enter_locked. simpl. now rewrite id_find_room.
Qed.
Lemma goal_enter_locked id state room2_id :
  (find_room (enter_locked state room2_id) id).(goal) = (find_room state id).(goal).
Proof.
  unfold enter_locked, find_room. simpl.
  destruct (state.(pos) =? id).
  - (* state pos が idのとき *) rewrite e.
    unfold app. rewrite(find_err_update_eq nat_eqDec id _ ).
    unfold room_unlock_door. simpl.
    now unfold current_room; rewrite e.
  - (* state.(pos) <> id のとき *)
    unfold app. rewrite find_err_update_neq; [|assumption].
    destruct (room2_id =? id).
    + (* room2_id = id の場合 *)
      rewrite e, find_err_update_eq.
      now unfold room_unlock_door.
    + (* room2_id <> id の場合 *)
      now rewrite find_err_update_neq.
Qed.


Inductive Next : State -> State -> Prop :=
| FreeDoor : forall room2_id state, FreeRoomOf (current_room state) room2_id ->
             Next state (enter_free state room2_id)
| Locked : forall state room2_id,
  state.(keys) >= 1 ->
  LockedRoomOf (current_room state) room2_id ->
  Next state (enter_locked state room2_id).

Inductive Reachable : State -> State -> Prop :=
| ReachableRefl : forall state, Reachable state state
| ReachableStep : forall state1 state1' state2,
    Next state1 state1' -> Reachable state1' state2 ->
    Reachable state1 state2.

Definition Solvable state :=
  exists state', Reachable state state' /\ (current_room state').(goal) = true.

Definition stage_of_list ls :=
  let table :=
    list_mapi (fun '(i, (goal, treasures, doors)) =>
                 (i, {| id:=i; goal:=goal; treasures:= treasures; doors:=doors|}))
      ls
  in
  {| table:=table; keys:=0; pos:=0; |}.

Lemma SolvableGoal state :
  (current_room state).(goal) = true -> Solvable state.
Proof.
  intros g. exists state. now split; [constructor | assumption].
Qed.

Lemma SolvableNext state state' :
    Next state state' -> Solvable state' ->
    Solvable state.
Proof.
  intros next [last [reach g]].
  exists last. split; [| now idtac].
  now apply (ReachableStep _ state').
Qed.

Lemma SolvableFree state next_room_id :
  Solvable (enter_free state next_room_id) ->
  FreeRoomOf (current_room state) next_room_id ->
  Solvable state.
Proof.
  intros g free.
  eapply SolvableNext; [| now apply g].
  now constructor.
Qed.

Lemma SolvableLocked state next_room_id n :
  state.(keys) = S n ->
(*  Solvable {| table:=state.(table); keys:=n; pos:=next_room |} ->*)
  Solvable (enter_locked state next_room_id) ->
  LockedRoomOf (current_room state) next_room_id ->
  Solvable state.
Proof.
  intros k g locked.
  eapply SolvableNext; [| now apply g].
  apply Locked; [| assumption].
  rewrite k. now auto with arith.
Qed.

Definition CantBeStuck init := forall state, Reachable init state -> Solvable state.


(* ============= 具体的なステージ =============== *)
Definition sample1 :=
  stage_of_list [
      (false, 0, [(true, 1); (false, 2)]); (*Start*)
      (true,  0, []); (*Goal*)
      (false, 1, [(false, 0)]) (*鍵のある部屋*)
    ].

Local Definition state2 := enter_free sample1 2.
Local Definition state3 := enter_free state2 0.
Local Definition last := enter_locked state3 1.

Theorem gsamp1 : Solvable sample1.
Proof.
  apply (SolvableFree _ (2)); [| now compute; right; left].
  fold state2.
  apply (SolvableFree _ (0)); [| now compute; left].
  fold state3.
  apply (SolvableLocked _ 1 0); [now compute | |now compute; left].
  apply SolvableGoal.
  now compute.
Qed.

Lemma CantBeStuckNext_Inv s1 s2 :
  Next s1 s2 -> CantBeStuck s1 -> CantBeStuck s2.
Proof.
  intros next cant state reach. apply cant.
  now apply ReachableStep with s2.
Qed.

Lemma CantBeStuckNext s1 :
  (exists s2, Next s1 s2) ->
  (forall s2, Next s1 s2 -> CantBeStuck s2) -> CantBeStuck s1.
Proof.
  unfold CantBeStuck.
  intros e H state reach.
  inversion reach.
(*  induction reach. *)
  - subst state0 state. destruct e as [s1' next]. apply SolvableNext with s1'; [now idtac|].
    apply H with s1'; [assumption|]. now constructor.
  - subst s1 state.
    now apply H with state1'.
Qed.

Lemma NextLast state : Next last state -> state = last.
Proof.
  unfold last. now inversion 1; [inversion H0 | inversion H1].
Qed.

Lemma ReachableLast state : Reachable last state -> state = last.
Proof.
  remember last. induction 1; [reflexivity|]. subst.
  now rewrite IHReachable; rewrite (NextLast _ H).
Qed.

Definition Invs state := (find_room state last.(pos)).(goal) = true.

Lemma SolvableLast state :
  Invs state -> state.(pos) = last.(pos) ->
  Solvable state.
Proof.
  intros. apply SolvableGoal. unfold current_room. now rewrite H0.
Qed.


Definition KeyStage state :=
  (find_room state last.(pos)).(goal) = true
  /\ (find_room state 0).(goal) = false
  /\ (find_room state 2).(goal) = false
  /\ state.(keys) >= 1
  /\ (find_room state 0).(doors) = [(true, 1); (false, 2)]
  /\ (find_room state 1).(doors) = []
  /\ (find_room state 2).(doors) = [(false, 0)]
  /\ (state.(pos) = 0 \/ state.(pos) = 2)
.

Definition Solved state := (current_room state).(goal) = true.

Lemma SolvedNext state1 state2 :
  doors (current_room state1) = [] ->
  Solved state1 -> Next state1 state2 ->
  state1 = state2.
Proof.
  intros ds sol next. inversion next.
  - unfold FreeRoomOf in H. now rewrite ds in H.
  - unfold LockedRoomOf in H0. now rewrite ds in H0.
Qed.


Lemma SolvedReachable state1 state2 :
  doors (current_room state1) = [] ->
  Solved state1 -> Reachable state1 state2 ->
  state1 = state2.
Proof.
  induction 3; [now idtac|].
  erewrite <- (SolvedNext _ _) in IHReachable; now auto.
Qed.


Lemma KeyStageNext state1 state2 :
  KeyStage state1 -> Next state1 state2 ->
  KeyStage state2 \/ Solved state2.
Proof.
  intros [goal1 [goal0 [goal2 [keys [doors0 [doors1 [doors2 p]]]]]]] next.
  destruct p as [room0 | room2 ].
  - (* Room 0 *) inversion next; subst.
    + (* 0 -> 2 に寄り道した場合*) left.
      repeat split.
      * now rewrite goal_enter_free.
      * now rewrite goal_enter_free.
      * now rewrite goal_enter_free.
      * rewrite keys_enter_free. now auto with arith.
      * now rewrite doors_enter_free.
      * now rewrite doors_enter_free.
      * now rewrite doors_enter_free.
      * right.
        rewrite pos_enter_free.
        unfold FreeRoomOf, current_room in H. rewrite room0,doors0 in H.
        now destruct H as [|[e |[]]]; [discriminate| injection e as e].
    + (* 0 -> ゴール の場合*) right.
      unfold LockedRoomOf, current_room in H0.
      rewrite room0, doors0 in H0.
      destruct H0 as [e| [|[]]]; [injection e as e|discriminate].
      unfold Solved, current_room.
      now rewrite <- e, goal_enter_locked, pos_enter_locked.
  - (* Room 2 *) left.
    inversion next; subst.
    + (* 1 -> 0 に進んだ場合 *)
      repeat split.
      * now rewrite goal_enter_free.
      * now rewrite goal_enter_free.
      * now rewrite goal_enter_free.
      * rewrite keys_enter_free. now auto with arith.
      * now rewrite doors_enter_free.
      * now rewrite doors_enter_free.
      * now rewrite doors_enter_free.
      * left. rewrite pos_enter_free.
        unfold FreeRoomOf, current_room in H. rewrite room2,doors2 in H.
        destruct H as [e|[]]. now injection e as e.
    + (* 1 -> lockドアに進むことはない *)
      unfold LockedRoomOf, current_room in H0.
      rewrite room2,doors2 in H0. now destruct H0 as [|[]].
Qed.

Lemma KeyStageReachable state1 state2 :
  KeyStage state1 -> Reachable state1 state2 ->
  KeyStage state2 \/ Solved state2.
Proof.
  induction 2; [now left |].
  destruct (KeyStageNext _ _ H H0).
  - (* state1 -> state1' で KS state' 保持するとき *)
    destruct (IHReachable H2).
    + (* state1' ->* state4 で KS state4 保持 *) now left.
    + (* Solved state4 なった場合 *) now right.
  - (* Solved state1' な場合 *) right.
    rewrite <- (SolvedReachable state1' state4); try assumption.
    destruct H as [goal1 [goal0 [goal2 [keys [doors0 [doors1 [doors2 p]]]]]]].
    destruct p as [pos0 | pos2].
    + (* Room0 -> の場合 *)
      inversion H0; subst.
      * (* 0 -> 2 の場合 2はSolvedじゃない *)
        unfold FreeRoomOf, current_room in H.
        rewrite pos0, doors0 in H. destruct H as [|[e|[]]]; [now idtac| injection e as e].
        subst room2_id. unfold Solved, current_room in H2.
        now rewrite goal_enter_free, pos_enter_free,goal2 in H2.
      * (* 0 -> 1 の場合: doorの数を計算 *)
        unfold LockedRoomOf, current_room in H3.
        rewrite pos0, doors0 in H3.
        destruct H3 as[e|[|[]]]; [injection e as e| discriminate]. subst room2_id.
        unfold current_room. rewrite pos_enter_locked.
        unfold enter_locked, app. rewrite pos0. simpl.
        now rewrite doors1.
    + (* Room2 -> の場合 *)
      inversion H0; subst.
      * (* free door : Solvedに矛盾*)
        unfold FreeRoomOf, current_room in H.
        rewrite pos2, doors2 in H.
        destruct H as [e|[]]. injection e as e. subst room2_id.
        unfold Solved, current_room in H2.
        now rewrite goal_enter_free, pos_enter_free, goal0 in H2.
      * (* locked door 矛盾 *)
        unfold LockedRoomOf, current_room in H3.
        rewrite pos2, doors2 in H3. now inversion H3.
Qed.

Lemma SolvableKeyStage state : KeyStage state -> Solvable state.
Proof.
  intros [goal1 [goal0 [goal2 [keys [doors0 [doors1 [doors2 p]]]]]]].
  destruct p.
  - (* Room0 鍵の前の部屋のとき *)
    exists (enter_locked state 1). split.
    + apply ReachableStep with (enter_locked state 1); [|now constructor].
      constructor; [assumption|].
      unfold LockedRoomOf. unfold current_room. rewrite H, doors0. now left.
    + unfold current_room.
      now rewrite goal_enter_locked, pos_enter_locked.
  - (* Room2 鍵を手に入れた直後 *)
    pose (enter_free state 0) as state'.
    pose (enter_locked state' 1) as state''.
    exists state''. split.
    + apply ReachableStep with state'.
      constructor. unfold FreeRoomOf, current_room. rewrite H, doors2. now left.
      apply ReachableStep with state''; [|now constructor].
      unfold state'.
      constructor; [unfold state'; rewrite keys_enter_free; auto with arith |].
      unfold LockedRoomOf. unfold current_room, state'.
      rewrite pos_enter_free, doors_enter_free, doors0. now left.
    + unfold state'', state', current_room.
      rewrite goal_enter_locked, goal_enter_free.
      now rewrite pos_enter_locked.
Qed.


Lemma KeyStage_state3 : KeyStage state3.
Proof.
  unfold state3. repeat split.
  now compute.
  now left.
Qed.

Theorem main : CantBeStuck sample1.
Proof.
(* sample1 *)
apply CantBeStuckNext; [now exists state2; constructor; compute; right; left|].
intros s2 next1. inversion next1; [|now compute in H]. subst state s2.
destruct H as [H | [H|[]]]; [discriminate| injection H as eroom2].
rewrite <- eroom2. fold state2.
(* state2 *)
apply CantBeStuckNext; [now exists state3; constructor; compute; left|].
intros s3 next2. inversion next2; [|now destruct H0 as [H0|[]]]. subst state s3.
destruct H as [H | []]. injection H as eroom3_id.
rewrite <- eroom3_id. fold state3.
(* state 3*)
  intros state reach.
  destruct (KeyStageReachable _ _ KeyStage_state3 reach).
  - now apply SolvableKeyStage.
  - now apply SolvableGoal.
Qed.
