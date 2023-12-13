Require Export Init.
Require Import Arith.PeanoNat.


Inductive clock : Set := nthClock : nat -> clock.
Definition toNat (c : clock) : nat := let 'nthClock n := c in n.

Lemma toNat_nthClock : ∀ n, toNat (nthClock n) = n.
Proof. trivial. Qed.

Lemma nthClock_toNat : ∀ c, nthClock (toNat c) = c.
Proof. intro. now destruct c. Qed.

Definition clock_eq_dec : ∀ c1 c2 : clock, {c1 = c2} + {c1 ≠ c2}.
Proof.
  intros.
  destruct c1 as [n1], c2 as [n2].
  destruct (Nat.eq_dec n1 n2) as [E | NE].
  - left. now rewrite E.
  - right. intro. apply NE. now injection H.
Defined.
