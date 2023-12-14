Require Import EventSpaces.Init.
Require Import EventSpaces.BasicNotions.
Require Import Arith.PeanoNat.

Lemma toNat_nthClock : ∀ n, toNat (nthClock n) = n.
Proof. trivial. Qed.

Lemma nthClock_toNat : ∀ c, nthClock (toNat c) = c.
Proof. intro. now destruct c. Qed.

Definition clock_eq_dec : ∀ c1 c2 : clock, {c1 = c2} + {c1 ≠ c2}.
Proof.
  intros. destruct c1 as [n1], c2 as [n2].
  destruct (Nat.eq_dec n1 n2).
  - rewrite e. now left.
  - right. intro.  apply n. now injection H.
Defined.

