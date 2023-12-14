Require Import EventSpaces.Init.
Import ListNotations.


Inductive clock := nthClock : nat → clock.
Coercion toNat (c : clock) : nat := let 'nthClock n := c in n.

Inductive increasing : list clock → Prop :=
  | inc0 : increasing []
  | inc1 : ∀ c, increasing [c]
  | incS : ∀ (c1 c2 : clock) cs,
      c1 < c2 → increasing (c2 :: cs) → increasing (c1 :: c2 :: cs).

Definition ClockSet := {cs : list clock | increasing cs}.
Coercion toList (cs : ClockSet) : list clock := proj1_sig cs.

Record event := mk_event {
  owner : clock;
  log_no : nat
}.