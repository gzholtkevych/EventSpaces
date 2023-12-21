Require Export Utf8.
Require Import Init.


Inductive clock : Set :=
  | some : clock
  | other : clock -> clock.

Fixpoint to_nat (c : clock) : nat :=
  match c with
  | some => 0
  | other c' => S (to_nat c')
  end.

Fixpoint from_nat (n : nat) : clock :=
  match n with
  | 0 => some
  | S n' => other (from_nat n')
  end.

Lemma to_from_nat : ∀ n, to_nat (from_nat n) = n.
Proof.
  intro.
  induction n as [| n' IHn'].
  - trivial.
  - simpl. now rewrite IHn'.
Qed.

Lemma from_to_nat : ∀ c, from_nat (to_nat c) = c.
Proof.
  intro.
  induction c as [| c' IHc'].
  - trivial.
  - simpl. now rewrite IHc'.
Qed.

Definition clock_eq_dec : ∀ c1 c2 : clock, {c1 = c2} + {c1 ≠ c2}.
Proof.
  intro.
  induction c1 as [| c1' IHc1'].
  - destruct c2 as [| c2'].
    + now left.
    + right. discriminate.
  - intro.
    induction c2 as [| c2' IHc2'].
    + right. discriminate.
    + destruct (IHc1' c2').
      * left. now rewrite e.
      * right. intro. apply n. now injection H. 
Defined.


Definition ClockSet :=
  {cs : clock → Prop | ∃ ecs : list clock, ∀ c, cs c → In c ecs}.
Definition toPredicate (cs : ClockSet) : clock → Prop := proj1_sig cs.
Coercion toPredicate : ClockSet >-> Funclass.