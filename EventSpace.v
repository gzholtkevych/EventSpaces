Require Export EventSpaces.Clocks.

Class anEventSet (event : clock -> nat -> Prop) := {
  finclock : ∃ n, ∀ c, id c ≥ n → ¬ (event c n);
  downward : ∀ c n, event c (S n) → event c n
}.

Class anEventSpace
  (event : clock → nat → Prop)
  `{anEventSet event}
  (prec : clock → nat → clock → nat → Prop) := {
  prec_irrefl : ∀ c n, ¬ prec c n c n;
  prec_trans :
    ∀ c1 n1 c2 n2 c3 n3, 
      prec c1 n1 c2 n2 → prec c2 n2 c3 n3 → prec c1 n1 c3 n3;
  local_linearity :
    ∀ c n1 n2, event c n1 → event c n2 → n1 < n2 ↔ prec c n1 c n2;
  finitenes2 :
    ∀ c n, event c n → ∃ N, ∀ m c', event c' m → prec c' m c n → m < N
}.
Check anEventSpace.

Structure eventSpace := mkEventSpace {
  event : clock → nat → Prop;
  eventSet_evidence : anEventSet event; 
  prec : clock → nat → clock → nat → Prop;
  event_guarantees : anEventSpace event prec
}.

