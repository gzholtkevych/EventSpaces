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

Fixpoint range_list(n m : nat) : list Atom :=
   match m with
   | 0 => []
   | S m' => a n :: range_list (S n) m'
   end.

Lemma inc_range_list : forall n m, increasing (range_list n m).
Proof.
  intros.
  destruct m as [| m'].
  - constructor.
  - revert n.
    induction m' as [| m'' IHm'']; intro.
    + constructor.
    + simpl in IHm'' |-*. constructor; [ constructor | apply IHm'' ].
Qed.

Lemma k_in_n_m : forall n m k, n <= k < n + m -> In (a k) (range_list n m).
Proof.
  intros until m. revert n.
  induction m as [| m' IHm']; intros.
  - destruct H as (Hle, Hlt). rewrite <- plus_n_O in Hlt.
    assert (k < k). { now apply Nat.le_trans with n. }
    exfalso. now apply Nat.lt_irrefl with k.
  - simpl. destruct H as (Hle, Hlt).
    destruct (lt_eq_lt_dec n k); try destruct s.
    + right. apply IHm'. split.
      * assumption.
      * rewrite plus_Sn_m. now rewrite <- plus_n_Sm in Hlt.
    + left. now rewrite e.
    + assert (k < k). { now apply Nat.le_trans with n. }
      exfalso. now apply Nat.lt_irrefl with k.
Qed.

Lemma n_m_holds_k : forall n m k, In (a k) (range_list n m) -> n <= k < n + m.
Proof.
  intros until m. revert n.
  induction m as [| m' IHm']; intros.
  - inversion H.
  - destruct H.
    + assert (n = k). { now injection H. }
      rewrite H0. split.
      * constructor.
      * rewrite <- plus_n_Sm. apply le_n_S. apply Nat.le_add_r.
    + pose (IH := IHm' (S n) k H). destruct IH as (Hle, Hlt).
      split.
      * now apply Nat.lt_le_incl.
      * rewrite <- plus_n_Sm. now rewrite plus_Sn_m in Hlt.
Qed.

Definition range (n m : nat) : AtomSet.
Proof. exists (range_list n m). exact (inc_range_list n m). Defined.

Definition ini_range(n : nat) : AtomSet := range 0 n.


