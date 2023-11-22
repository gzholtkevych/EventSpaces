Require Import EventSpaces.Atoms.

Class anEventSet
  (event : Atom -> nat -> Set) :=
{ downward : forall x n m, event x n -> m < n -> event x m;
  finsrc : exists N, forall x n, event x n -> id x <= N
}.