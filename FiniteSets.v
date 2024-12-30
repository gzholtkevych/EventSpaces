Require Import DisCo.Enum_modular.
(* Require Import Coq.Arith.Cantor. *)

(* Here, the concepts of a participant identifier and
   an event tag is introduced *)

Inductive PID (* type of participant IDs *) : Set := Pid : nat -> PID.
Notation "# x" := (Pid x)  (at level 25, format "'#' x").

Module EnumPID.
  Definition universe := PID.
  Definition tonat := fun p : PID => let '#n := p in n.
  Lemma tonat_inj : forall x y, tonat x = tonat y -> x = y.
  (* tonat is injective *)
  Proof.
    intros. destruct x as (nx), y as (ny). simpl in H.
    now rewrite H.
  Qed.
End EnumPID.

Module FSetPID := FSet(EnumPID).


Record EventTag (* an event tag is determined by *) : Set :=
{ pid (* the participant that observes the event *) : PID
; num (* number of the event in the ledger of this participant *) : nat
}.

(*
  Local Definition to2nat (e : EventTag) (*
    transforms an event tag into a pair of natural numbers *) : nat * nat :=
  let '{| pid := p; num := n |} := e in
  let 'Pid ip := p in (ip, n).

  Local Definition tonat' (*
    encodes an event tag using Cantor pairing function *) : EventTag -> nat :=
  fun e => to_nat (to2nat e).


  Instance Enum_EventTag (* EventTag is an enumerable set *) : Enum EventTag.
  Proof.
    constructor 1 with (tonat := tonat'). unfold tonat'.
    intros e1 e2 H.
    assert (H' : to2nat e1 = to2nat e2). {
      now apply (to_nat_inj (to2nat e1) (to2nat e2)). }
    destruct e1 as (p1, n1), e2 as (p2, n2). simpl in H'.
    destruct p1 as (ip1), p2 as (ip2).
    f_equal; f_equal; now injection H'.
  Defined.
*)

