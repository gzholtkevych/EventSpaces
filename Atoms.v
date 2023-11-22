Require Import Lists.List.
Import ListNotations.


Inductive Atom := a : nat -> Atom.

Definition id (x : Atom) : nat := let 'a n := x in n.


Inductive increasing : list Atom -> Prop :=
  | inc0 : increasing []
  | inc1 : forall x, increasing [x]
  | incS :
      forall x y xs,
        id x < id y -> increasing (y :: xs) -> increasing (x :: y :: xs).

Definition AtomSet := {xs : list Atom | increasing xs}.
Coercion to_list (xs : AtomSet) : list Atom := proj1_sig xs.
