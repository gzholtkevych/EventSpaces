Require Import EventSpaces.EventSpace.
Require Arith.Compare_dec.
Require Arith.PeanoNat.


Example noevent : eventSpace.
Proof.
  pose (event := fun (c : clock) (n : nat) => False).
  assert (anEventSet event). {
    constructor.
    - exists 0. intros. now compute.
    - intros. now compute in H |-*. }
  pose (prec := fun (c1 : clock) (n1 : nat) (c2 : clock) (n2 : nat) => False).
  apply (mkEventSpace event H prec).
  constructor; try now compute.
Defined.


Module Counter.
Import Arith.PeanoNat.

  Example counter (c₀ : clock) : eventSpace.
  Proof.
    pose (event := fun (c : clock) (n : nat) => c = c₀).
    assert (anEventSet event). {
      constructor.
      - exists (S (id c₀)). intros. intro.
        compute in H0. rewrite H0 in H. unfold "_ ≥ _" in H.
        now apply Nat.lt_irrefl with (x := id c₀).
      - intros. now compute in H |-*. }
    pose (prec (c1 : clock) (n1 : nat) (c2 : clock) (n2 : nat) :=
      c1 = c2 ∧ n1 < n2).
    apply (mkEventSpace event H prec).
    constructor.
    - intros. intro. compute in H0. destruct H0.
      now apply Nat.lt_irrefl with n.
    - intros. compute in H0, H1 |-*.
      destruct H0, H1. split.
      + now rewrite H0, -> H1.
      + now apply Nat.lt_trans with n2.
    - intros. split; intro.
      + compute. split; auto.
      + compute in H2. now destruct H2.
    - intros. exists n. intros. compute in H2.
      now destruct H2.
  Defined.
End Counter.  
