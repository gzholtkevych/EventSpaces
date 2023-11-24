Require Import Lists.List.
Import ListNotations.
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.


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

Fixpoint range(n m : nat) : list Atom :=
   match m with
   | 0 => []
   | S m' => a n :: range (S n) m'
   end.

Lemma k_in_range_n_m : forall n m k, n <= k < n + m -> In (a k) (range n m).
Proof.
  intros *. revert n k.
  induction m as [| m' IHm']; intros.
  - destruct H as (H1, H2).
    assert (H3 : n < n). {
      apply Nat.lt_trans with k.
      - unfold "_ < _".
  - destruct H as (H1, H2). simpl.
    assert (H3 : k <= m'). { unfold "_ < _" in H2. now apply le_S_n. }
    clear H2.
    assert ({k = m'} + {S n <= k < m'} + {n = k}). {
      destruct (le_lt_eq_dec n k H1).
      - left. destruct (le_lt_eq_dec k m' H3).
        + right.  split; assumption.
        + now left.
      - now right. }
    destruct H.
    + destruct s.
      * right. apply IHm'. admit.
      * right. now apply IHm'.
    + left. now rewrite e.

Definition ininat (n : nat) : list Atom := range 0 n.

Lemma ininnat_inc : forall n, increasing (ininat n).
Proof.
  intro.
  induction n as [| n' IHn'].
  - constructor.
  - simpl.
    destruct IHn'.
    + constructor.
    + 