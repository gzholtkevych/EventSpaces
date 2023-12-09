Require Export Utf8.
Require Import Arith.PeanoNat.


Inductive clock := clk : nat -> clock.
Definition id (c : clock) : nat := let 'clk n := c in n.

Lemma id_clk : ∀ n, id (clk n) = n.
Proof. trivial. Qed.

Lemma clk_id : ∀ c, clk (id c) = c.
Proof. intro. now destruct c as [n]. Qed.

Definition clock_eq_dec : ∀ c1 c2 : clock, {c1 = c2} + {c1 ≠ c2}.
Proof.
  intros.
  destruct c1 as [n1], c2 as [n2].
  destruct (Nat.eq_dec n1 n2) as [E | NE].
  - left. now rewrite E.
  - right. intro. apply NE. now injection H.
Defined.
