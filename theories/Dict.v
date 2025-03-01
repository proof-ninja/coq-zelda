Require Import List Sumbool.
Import ListNotations.
Require Import Common Eq.

Set Implicit Arguments.

Section Dict.

Variable KDec : eqDec.
Definition K := KDec.(sort).
Variables V : Type.
(*Variable eq_key_dec : forall (x y: K), {x = y} + {x <> y}.*)


Definition t := list (K * V).

Definition empty : t := [].

Definition find (key: K) (dict : t) : option V :=
  let opt :=
    List.find
      (fun '(k,v) => if k =? key then true else false)
      dict
  in
  option_map snd opt.


Definition find_err (dict: t) (default:V) key : V :=
  find key dict
  |> option_value default.

Definition delete key dict : t :=
  List.filter (fun '(k,v) =>
                 if k =? key then false
                 else true) dict.

Definition update key value dict : t :=
  (key, value) :: (delete key dict).

Definition size (dict: t) : nat :=
  List.length dict.

Definition Forall (P: K -> V -> Prop) (dict: t) : Prop :=
  List.Forall (fun '(k, v) => P k v) dict.

Definition Forall_dec (P: K -> V -> Prop) (P_dec: forall (k: K) (v: V), {P k v} + {~P k v}) dict:
  {Forall P dict} + {~Forall P dict}.
refine (List.Forall_dec (fun '(k, v) => P k v) (fun '(k, v) => P_dec k v) dict).
Defined.

Definition Equiv_listset {A: Type} (xs ys: list A) :=
  List.incl xs ys /\ List.incl ys xs.

Definition keys (dict: t) := List.map fst dict.

Lemma find_update k v dict :
  find k (update k v dict) = Some v.
Proof.
  unfold find, update. simpl. now destruct (k =? k).
Qed.

Lemma list_find_filter {A:Type} (f g : A -> bool) (xs: list A):
  (forall x, f x = true -> g x = true) ->
  List.find f (filter g xs) = List.find f xs.
Proof.
  induction xs; [now idtac|].
  intros fg. simpl.
  case_eq (f a); intros fa.
  - rewrite (fg _ fa). simpl. now rewrite fa.
  - case_eq (g a); intros ga; simpl.
    + now rewrite fa, IHxs.
    + now rewrite IHxs.
Qed.

Lemma find_update_other k v dict k':
  k <> k' ->
  find k' (update k v dict) = find k' dict.
Proof.
  intros neq. unfold find, update, delete. simpl.
  destruct (k =? k'); [now auto|].
  f_equal. rewrite list_find_filter; [now idtac|].
  intros [k0 _].
  destruct (k0 =? k'), (k0 =? k); try auto. now subst.
Qed.

Lemma find_err_update_eq k v dict err:
  find_err (update k v dict) err k = v.
Proof.
  unfold find_err. now rewrite find_update.
Qed.
Lemma find_err_update_neq k v dict err k':
  k <> k' -> find_err (update k v dict) err k' = find_err dict err k'.
Proof.
  intros neq. unfold find_err. now rewrite find_update_other.
Qed.

Definition Equiv (x y: t) : Prop :=
  Equiv_listset (keys x) (keys y)
  /\ List.Forall (fun key => find key x = find key y) (keys x).
Lemma Equiv_refl x : Equiv x x.
Proof.
  repeat split.
  - now apply incl_refl.
  - now apply incl_refl.
  - now apply Forall_forall.
Qed.

Axiom eq_equiv : forall (x y: t), Equiv x y -> x = y.

End Dict.
