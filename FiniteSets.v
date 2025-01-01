Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import Lists.List.


Class Enum (X : Set) :=
{ tonat : X -> nat
; tonat_inj : forall x y, tonat x = tonat y -> x = y
}.


Definition eq_dec {X : Set} `{Enum X} : forall x y : X, {x = y} + {x <> y}.
Proof.
  intros.
  destruct (Nat.eq_dec (tonat x) (tonat y)) as [H0 | H0]; [left | right].
  - now apply tonat_inj.
  - intro H'. apply H0. now rewrite H'.
Defined.


Section FSetDefinitions.
Variable X : Set.
Context `{Enum X}.

  Inductive increasing : list X -> Prop :=
  | inc_nil : increasing nil
  | inc_sol : forall x, increasing (x :: nil)
  | inc_cons : forall x y lst,
      tonat x < tonat y -> increasing (y :: lst) -> increasing (x :: y :: lst).

  Local Lemma increasing_tail :
    forall x lst, increasing (x :: lst) -> increasing lst.
  Proof. intros. inversion_clear H0; constructor || assumption. Qed.

  Definition FSet := {lst : list X | increasing lst}.

End FSetDefinitions.
Arguments increasing {X} {_}.
Coercion tolist {X : Set} `{Enum X} (A : FSet X) : list X := proj1_sig A.


Definition In_dec {X : Set} `{Enum X} (x : X) (A : FSet X) :
  {In x A} + {~ In x A}.
Proof.
  destruct A as (lst, H0). simpl.
  induction lst as [| y lst' IHlst']; simpl.
  - right. intro. contradiction.
  - destruct (eq_dec y x) as [H1 | H1].
    + left. now left.
    + assert (H2 : {In x lst'} + {~ In x lst'}). {
        apply IHlst'. now apply increasing_tail with y. }
      destruct H2 as [H2 | H2].
      * left. now right.
      * right. intro H3. elim H3; trivial.
Defined.


Section AddOperation.
Variable X : Set.
Context `{Enum X}.

  Fixpoint aux_add (x : X) (lst : list X) : list X :=
    match lst with
    | nil       => x :: nil
    | y :: lst' => match lt_eq_lt_dec (tonat x) (tonat y) with
        | inleft Hle => match Hle with
            | left _  => x :: y :: lst'
            | right _ => y :: lst'
            end
        | inright _  => y :: (aux_add x lst')
        end
    end.

  Lemma aux_add_keeps_increasing :
    forall x lst, increasing lst -> increasing (aux_add x lst).
  Proof.
    intros *.
    destruct lst as [| y lst'].
    - intros. constructor.
    - intros. simpl.
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now constructor.
      + assumption.
      + revert y H0 Hgt.
        induction lst' as [| z lst'' IHlst'']; intros; simpl.
        * constructor; constructor || assumption.
        * destruct (lt_eq_lt_dec (tonat x) (tonat z)) as [Hle | Hgt'];
          try destruct Hle as [Hlt | Heq]; constructor; trivial;
          try constructor; trivial;
          try (now apply increasing_tail with y);
          try (inversion_clear H0; trivial).
          now apply IHlst''.
  Qed.

  Definition add (x : X) (A : FSet X) : FSet X.
  Proof.
      destruct A as (lst, H0).
      exists (aux_add x lst).
      destruct lst as [| y lst'].
      - constructor.
      - now apply aux_add_keeps_increasing.
  Defined.

  Lemma add_In : forall x A, In x (add x A).
  Proof.
    intros.
    destruct A as (lst, H0). simpl.
    induction lst as [| y lst' IHlst'].
    - now left.
    - simpl.
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now left.
      + left. symmetry. now apply H.
      + right. apply IHlst'. now apply increasing_tail with y.
  Qed. 

End AddOperation.
Arguments add {X} {_}.


Definition size {X : Set} `{Enum X} (A : FSet X) : nat := length A.


Definition empty {X : Set} `{Enum X} : FSet X.
Proof. exists nil. constructor. Defined.


Fixpoint fromlist {X : Set} `{Enum X} (lst : list X) : FSet X :=
  match lst with
  | nil => empty
  | x :: lst' => add x (fromlist lst')
  end.


Section RemoveOperation.
Variable X : Set.
Context `{Enum X}.

  Fixpoint aux_remove (x : X) (lst : list X) : list X :=
    match lst with
    | nil       => nil
    | y :: lst' => match eq_dec x y with
        | left _  => lst'
        | right _ => y :: (aux_remove x lst')
        end
    end.

  Lemma aux_remove_keeps_increasing :
    forall x lst, increasing lst -> increasing (aux_remove x lst).
  Proof.
    intros.
    induction lst as [| y lst' IHlst'].
    - constructor.
    - destruct lst' as [| z lst''].
      * simpl. destruct (eq_dec x y) as [H1 | H1]; constructor.
      * assert (H1 : increasing (aux_remove x (z :: lst''))). {
          apply IHlst'. now apply increasing_tail with y. }
        simpl in H1 |-*. destruct (eq_dec x y) as [H2 | H2];
        destruct (eq_dec x z) as [H3 | H3];
        try (now apply increasing_tail with y).
        2 : { constructor; trivial. now inversion_clear H0. }
        inversion_clear H0.
        destruct lst'' as [| u lst''']; constructor.
        2 : { now apply increasing_tail with z. }
        apply Nat.lt_trans with (tonat z); trivial.
        now inversion_clear H5.
  Qed.

  Definition remove (x : X) (A : FSet X) : FSet X.
  Proof.
    destruct A as (lst, H0).
    exists (aux_remove x lst).
    now apply aux_remove_keeps_increasing.
  Defined.

  Lemma remove_not_In : forall x A, ~ In x (remove x A).
  Proof.
    intros * N. destruct A as (lst, H0). simpl in N.
    induction lst as [| y lst' IHlst'].
    - simpl in N. contradiction.
    - destruct lst' as [| z lst''].
      * 
      + now apply increasing_tail with y.
      + assert (H1 : In x (aux_remove x lst') -> False). {
          apply IHlst'. now apply increasing_tail with y. }
        simpl in N. destruct (eq_dec x y) as [H2 | H2];
        destruct lst' as [| z lst''].
        * contradiction.
        * simpl in N. destruct N as [H3 | H3].
          -- rewrite H3 in H1. rewrite H3.
             simpl in H1 |-*. destruct (eq_dec x x). contradict H1. 

 simpl in N. destruct (eq_dec x y) as [H1 | H1].
        destruct lst' as [| z lst''].
        * contradiction.
        * simpl. destruct (eq_dec x z) as [H2 | H2].
          2 : { simpl in N |-*.

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
