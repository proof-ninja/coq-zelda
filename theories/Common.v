Require Import List.
Import ListNotations.

Definition app {A B: Type} (f: A -> B) x := f x.
Notation "x |> f" := (app f x) (at level 50).

Definition option_value {A: Type} default (o: option A) :=
  match o with
  | None => default
  | Some x => x
  end.

Fixpoint list_make_aux {A: Type} (store: list A) (f: nat -> A) len : list A :=
  match len with
  | S n => list_make_aux (f (S n) :: store) f n
  | O => List.rev store
  end.
Definition list_make {A:Type} f len := @list_make_aux A [] f len.

Definition list_with_index {A:Type} (xs: list A) : list (nat * A) :=
  List.fold_left (fun '(i, store) x =>
                    (S i, (i,x)::store)) xs (0, [])
  |> snd.

Definition list_mapi {A B: Type} (f: nat * A -> B) xs : list B :=
  List.map f (list_with_index xs).
