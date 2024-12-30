Require Import DisCo.Atoms_modular.
Require Import Coq.Lists.List.

Notation FSet := FSetPID.type (only parsing).
Notation size := FSetPID.size (only parsing).
(* Notation tolist := FSetPID.tolist  (only parsing). *)
Coercion FSetPID.tolist : FSet >-> list.


Section DiagramClass.
Variable participants : FSet.
(* refers to the set of diagram participants *)
Variable event : EventTag -> Prop.
(* picks events related to the diagram *)
Variable sending : EventTag -> option EventTag.
(* refers to the corresponding sending event if the argument is
   a receiving event *)

  Class aDiagram : Prop :=
  (* gathers the constraints relevant to the diagram cocept *)
  { at_least_two : size participants >= 2
    (* number of participants is at least two *)
  ; only_participants : forall e, event e -> In (pid e) participants
    (* each event related to a diagram is entered in the register of
       some diagram participant *) 
  ; gaplessness :
      forall e n, event e -> n < num e -> event {| pid := pid e; num := n |}
    (* numbering in each register of a participant has no gap *)
  ; sending_dom : forall e, sending e <> None -> event e
    (* 'sending' is defined only for events related to the diagram but
       perhaps not for all *)
  ; sending_cod : forall e e', sending e = Some e' -> event e'
    (* 'sending' ranges only over events related to the diagrams but
       perhaps not all *)
  ; lack_of_sending_to_itself :
      forall e e', Some e = sending e' -> pid e <> pid e'
    (* there is no manner to send a message from a participant to itself *)
  ; sending_injectivity :
      forall e' e'' e, Some e = sending e' -> Some e = sending e'' -> e' = e''
    (* each sending event corresponds exactly one receiving event *)
  }.
End DiagramClass.


Structure Diagram :=
{ participants : FSet
; event : EventTag -> Prop
; sending : EventTag -> option EventTag
; diagram_guarantees : aDiagram participants event sending
}.
