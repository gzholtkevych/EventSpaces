Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import Lists.List.


Module Type TEnum.
  Parameter universe : Set.
  Parameter tonat : universe -> nat.
  Axiom tonat_inj : forall x y, tonat x = tonat y -> x = y.  
End TEnum.


Module FSet (M : TEnum) <: TEnum.
Include M.

  Definition eq_dec : forall x y : universe, {x = y} + {x <> y}.
  Proof.
    intros.
    destruct (Nat.eq_dec (tonat x) (tonat y)) as [H | H]; [left | right].
    - now apply tonat_inj.
    - intro H'. apply H. now rewrite H'.
  Defined.

  Inductive increasing : list universe -> Prop :=
  | inc0 : increasing nil
  | inc1 : forall x : universe, increasing (x :: nil)
  | incS : forall x y (lst : list universe),
      tonat x < tonat y -> increasing (y :: lst) -> increasing (x :: y :: lst).

  Definition type := {lst : list universe | increasing lst}.

  Definition tolist (A : type) : list universe := proj1_sig A.
  Coercion tolist : type >-> list.

  Definition size (A : type) : nat := length A.

  Definition empty : type.
  Proof. exists nil. constructor. Defined.

  Fixpoint aux_push (x : universe) (lst : list universe) : list universe.
  Proof.
    destruct lst as [| y lst'] eqn: E.
    - exact (x :: nil).
    - destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + exact (x :: lst).
      + exact lst.
      + exact (y :: (aux_push x lst')).
  Defined.

  Definition push (x : universe) (A : type) : type.
  Proof.
    destruct A as (lst, H).
    exists (aux_push x lst).
    destruct lst as [| y lst'].
    - constructor.
    - simpl.
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + constructor; trivial.
      + assumption.
      + revert x y H Hgt. induction lst' as [| y' lst'' IHlst'']; intros.
        constructor; assumption || constructor.
        simpl in IHlst'' |-*.
        destruct (lt_eq_lt_dec (tonat x) (tonat y')) as [Hle | Hgt'];
        try destruct Hle as [Hlt | Heq]; try constructor; trivial;
        try constructor; trivial; try constructor; trivial;
        try inversion_clear H; trivial.
        apply IHlst''; trivial.
  Defined.

  Fixpoint totype (lst : list universe) : type :=
    match lst with
    | nil => empty
    | x :: lst' => push x (totype lst')
    end.

End FSet.
