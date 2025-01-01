Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import Lists.List.


Module Type TEnum.
  Parameter universe : Set.
  Parameter tonat : universe -> nat.
  Axiom tonat_inj : forall x y, tonat x = tonat y -> x = y.  
End TEnum.

Module Enum (M : TEnum) <: TEnum.
Definition universe := M.universe.
Definition tonat := M.tonat.
Definition tonat_inj := M.tonat_inj.

  Definition eq_dec : forall x y : universe, {x = y} + {x <> y}.
  Proof.
    intros.
    destruct (Nat.eq_dec (tonat x) (tonat y)) as [H | H]; [left | right].
    - now apply tonat_inj.
    - intro H'. apply H. now rewrite H'.
  Defined.

End Enum.


Module FSet (M : TEnum) <: TEnum.
Module EnumM := Enum(M).
Include EnumM.

  Inductive increasing : list universe -> Prop :=
  | inc0 : increasing nil
  | inc1 : forall x : universe, increasing (x :: nil)
  | incS : forall x y (lst : list universe),
      tonat x < tonat y -> increasing (y :: lst) -> increasing (x :: y :: lst).

  Local Lemma increasing_tail :
    forall x lst, increasing (x :: lst) -> increasing lst.
  Proof. intros. inversion_clear H; constructor || assumption. Qed.

  Fixpoint aux_push (x : universe) (lst : list universe) : list universe :=
    match lst with
    | nil       => x :: nil
    | y :: lst' => match lt_eq_lt_dec (tonat x) (tonat y) with
        | inleft Hle => match Hle with
            | left _  => x :: y :: lst'
            | right _ => y :: lst'
            end
        | inright _  => y :: (aux_push x lst')
        end
    end.

  Lemma aux_push_keeps_increasing :
    forall x lst, increasing lst -> increasing (aux_push x lst).
  Proof.
    intros *. revert x.
    destruct lst as [| y lst'].
    - intros. constructor.
    - intros. simpl.
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now constructor.
      + assumption.
      + revert y H Hgt.
        induction lst' as [| z lst'' IHlst'']; intros; simpl.
        * constructor; constructor || assumption.
        * destruct (lt_eq_lt_dec (tonat x) (tonat z)) as [Hle | Hgt'];
          try destruct Hle as [Hlt | Heq]; constructor; trivial;
          try constructor; trivial;
          try apply increasing_tail with y; trivial;
          try rewrite Heq in Hgt; trivial;
          try inversion_clear H; trivial.
          constructor; trivial.
          now apply IHlst''.
  Qed.

  Definition type := {lst : list universe | increasing lst}.

  Definition tolist (A : type) : list universe := proj1_sig A.
  #[global] Coercion tolist : type >-> list.


  Definition size (A : type) : nat := length A.

  Definition empty : type.
  Proof. exists nil. constructor. Defined.

  Section Operation_push.
  Variable x : universe.

    Definition push (A : type) : type.
    Proof.
      destruct A as (lst, H).
      exists (aux_push x lst).
      destruct lst as [| y lst'].
      - constructor.
      - now apply aux_push_keeps_increasing.
    Defined.

  End Operation_push.

  Fixpoint totype (lst : list universe) : type :=
    match lst with
    | nil => empty
    | x :: lst' => push x (totype lst')
    end.

  Definition In_dec (x : universe) (A : type) : {In x A} + {~ In x A}.
  Proof.
    pose (Dec := EnumM.eq_dec).
    destruct A as (lst, H). simpl.
    induction lst as [| y lst' IHlst']; simpl.
    - right. intro. contradiction.
    - assert (increasing lst'). { now apply increasing_tail with y. }
      destruct Dec with y x as [H1 | H1].
      + left. now left.
      + destruct (IHlst' H0) as [H2 | H2].
        * left. now right.
        * right. intro H3. elim H3; trivial.
  Defined.

  Definition remove (x : universe) (A : type) : type.
  Proof.
    destruct A as (lst, H0).
    induction lst as [| y lst' IHlst'].
    + exact empty.
    + destruct EnumM.eq_dec with x y as [H | H].
      * exists lst'. now apply increasing_tail with y.
      * assert (H1 : increasing lst'). { now apply increasing_tail with y. }
        exact (push y (IHlst' H1)).
  Defined.

End FSet.


Module EnumNat <: TEnum.
Definition universe := nat.
Definition tonat := fun n : universe => n.
Lemma tonat_inj : forall n m, tonat n = tonat m -> n = m.
Proof. intros. unfold tonat in H. assumption. Qed.
End EnumNat.

Print EnumNat.universe.

Module FSetNat := FSet(EnumNat).
Coercion FSetNat.tolist : FSetNat.type >-> list.

Example set := FSetNat.totype (5 :: 4 :: 3 :: 2 :: 1 :: 0 :: nil).
Eval compute in FSetNat.tolist set.
Eval simpl in FSetNat.tolist (FSetNat.remove 4 set).
