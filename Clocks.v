Require Import Utf8.
Require Import Arith.PeanoNat.
Require Import Lists.List.
Import ListNotations.


Inductive clock : Set :=
  | some_clock : clock
  | other_clock : clock → clock.

Fixpoint nth_clock (n : nat) : clock :=
  match n with
  | 0 => some_clock
  | S n' => other_clock (nth_clock n')
  end.

Lemma nth_clock_inj : ∀ n m, nth_clock n = nth_clock m → n = m.
Proof.
  intro.
  induction n as [| n' IHn'].
  - intros. simpl in H.
    destruct m as [| m']; [ reflexivity | simpl in H; discriminate H ].
  - intro. revert n' IHn'.
    destruct m as [| m']; intros.
    + simpl in H. discriminate H.
    + simpl in H.
      assert (nth_clock n' = nth_clock m'). now  injection H.
      assert (n' = m'). now apply IHn'. now rewrite H1.
Qed.

Lemma nth_clock_surj : ∀ c : clock, ∃ n, c = nth_clock n.
Proof.
  intro.
  induction c as [| c' IHc'].
  - exists 0. reflexivity.
  - destruct IHc' as [n']. exists (S n'). rewrite H. reflexivity.
Qed.

Definition clock_eq_dec : ∀ c1 c2 : clock, {c1 = c2} + {c1 ≠ c2}.
Proof.
  intros. induction c1 as [| c1' IHc1'].
    destruct c2.
      now left.
      right. intro. discriminate H.
    revert c1' IHc1'. induction c2; intros.
      

    induction c1 as [| c1' IHc1']; intro.
      right. intro. discriminate H.
    + right. rewrite e. intro. inversion_clear H.
(*
Section AtomSets.
Variables
  (atom : Set)
  (from_nat : nat → atom)
  (to_nat : atom →  nat).
Context `{atom_is_Atom : Atom atom from_nat to_nat}.

  Definition AtomSet :=
    {f : atom → Prop | ∃ n : nat, ∀ a, f a → to_nat a ≤ n}.

  Definition 

End AtomSets.
*)