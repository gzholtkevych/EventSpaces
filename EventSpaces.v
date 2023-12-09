Require Import EventSpaces.Clocks.
Require Arith.Compare_dec.

Class anEventSet (event : clock → nat → Set) := {
  finclock : ∃ n, ∀ c m, event c m → id c ≤ n;
  downward : ∀ c n, event c (S n) -> event c n
}.

Class anEventSpace
  (event : clock → nat → Set)
  `{anEventSet event}
  (prec : clock → nat → clock → nat → Prop) := {
  prec_irrefl : ∀ c n, ¬ prec c n c n;
  prec_trans :
    ∀ c1 n1 c2 n2 c3 n3, 
      prec c1 n1 c2 n2 → prec c2 n2 c3 n3 → prec c1 n1 c3 n3;
  local_linearity :
    ∀ c n1 n2, event c n1 → event c n2 → n1 < n2 → prec c n1 c n2;
  finitenes2 :
    ∀ c n, event c n → ∃ N, ∀ m c', event c' m → prec c' m c n → m ≤ N
}.
Check anEventSpace.

Structure eventSpace := mkEventSpace {
  event : clock → nat → Set;
  eventSet_evidence : anEventSet event; 
  prec : clock → nat → clock → nat → Prop;
  event_guarantees : anEventSpace event prec
}.
Check eventSpace.

Module Examples.
Import Arith.Compare_dec.

Example conc3 : eventSpace.
Proof.
  assert (event : clock → nat → Set). {
    exact fun 
  constructor.
  intros c n.
  destruct (lt_eq_lt_dec n 3) as [Hle | Hgt]; try destruct Hle as [Hlt | Heq].
  - exact unit.
  - exact Empty_set.
  - exact Empty_set.
Qed.
Eval simpl in frame3 (clk 10) 5.