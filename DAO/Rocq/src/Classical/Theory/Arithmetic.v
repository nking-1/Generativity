(** * Arithmetic in ClassicalAlphaType
    
    This module builds arithmetic operations on top of natural numbers. *)

Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaAPI.
Require Import DAO.Classical.Theory.NaturalNumber.
Import ClassicalAlphaAPI.
Import NaturalNumber.

Module Arithmetic.
  Section Definitions.
    Context `{H_alpha: ClassicalAlphaType}.
    
    (** Import natural number components *)
    Context (IsNat : AlphaPred) (IsZero : AlphaPred) 
            (Succ : Alphacarrier -> Alphacarrier -> Prop).
    Context (zero_exists : exists z, IsZero z /\ IsNat z).
    Context (zero_unique : forall x y, IsZero x -> IsZero y -> x = y).
    Context (successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y).
    Context (successor_functional : forall x y z, Succ x y -> Succ x z -> y = z).
    Context (successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y).
    Context (zero_not_successor : forall x y, IsZero y -> ~ Succ x y).
    Context (nat_induction : forall (P : AlphaPred),
        (forall z, IsZero z -> P z) ->
        (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
        (forall n, IsNat n -> P n)).
    Context (zero : Alphacarrier).
    Context (zero_is_zero : IsZero zero).
    Context (zero_is_nat : IsNat zero).
    
    (** ** Basic Definitions *)
    
    (** Define One as successor of zero *)
    Definition IsOne : AlphaPred := fun x => exists z, IsZero z /\ Succ z x.
    
    (** ** Arithmetic Operations *)
    
    (** Addition relation: Plus x y z means x + y = z *)
    Variable Plus : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.
    
    (** Addition axioms *)
    Axiom plus_zero_left : forall x z, IsZero z -> IsNat x -> Plus z x x.
    Axiom plus_zero_right : forall x z, IsZero z -> IsNat x -> Plus x z x.
    Axiom plus_successor : forall x y z sx sy sz,
      IsNat x -> IsNat y -> IsNat z ->
      Succ x sx -> Succ y sy -> Succ z sz ->
      Plus x y z -> Plus sx y sz.
    Axiom plus_functional : forall x y z1 z2,
      Plus x y z1 -> Plus x y z2 -> z1 = z2.
    Axiom plus_exists : forall x y,
      IsNat x -> IsNat y -> exists z, IsNat z /\ Plus x y z.
    Axiom plus_comm : forall x y z,
      Plus x y z -> Plus y x z.
    
    (** Multiplication relation: Times x y z means x * y = z *)
    Variable Times : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.
    
    (** Multiplication axioms *)
    Axiom times_zero_left : forall x z, IsZero z -> IsNat x -> Times z x z.
    Axiom times_zero_right : forall x z, IsZero z -> IsNat x -> Times x z z.
    Axiom times_one_left : forall x o, IsOne o -> IsNat x -> Times o x x.
    Axiom times_one_right : forall x o, IsOne o -> IsNat x -> Times x o x.
    Axiom times_successor : forall x y z xy sxy,
      IsNat x -> IsNat y -> IsNat z ->
      Succ y z ->
      Times x y xy -> Plus xy x sxy ->
      Times x z sxy.
    Axiom times_functional : forall x y z1 z2,
      Times x y z1 -> Times x y z2 -> z1 = z2.
    Axiom times_exists : forall x y,
      IsNat x -> IsNat y -> exists z, IsNat z /\ Times x y z.
    
    (** ** Derived Concepts *)
    
    (** Divisibility: Divides d n means d divides n *)
    Definition Divides (d n : Alphacarrier) : Prop :=
      exists q, IsNat q /\ Times d q n.
    
    (** Prime numbers *)
    Definition IsPrime (p : Alphacarrier) : Prop :=
      IsNat p /\
      ~ IsZero p /\
      ~ IsOne p /\
      forall d, IsNat d -> Divides d p -> (IsOne d \/ d = p).
    
    (** Greater than relation *)
    Definition Greater (x y : Alphacarrier) : Prop :=
      exists z, IsNat z /\ ~ IsZero z /\ Plus y z x.
    
    (** ** Basic Theorems *)
    
    (** One exists and is unique *)
    Lemma one_exists : exists o, IsOne o /\ IsNat o.
    Proof.
      destruct zero_exists as [z [Hz HzNat]].
      destruct (successor_exists z HzNat) as [o [Hsucc HoNat]].
      exists o. split.
      - exists z. split; assumption.
      - exact HoNat.
    Qed.
    
    Lemma one_unique : forall x y, IsOne x -> IsOne y -> x = y.
    Proof.
      intros x y [zx [Hzx Hsuccx]] [zy [Hzy Hsuccy]].
      assert (zx = zy) by (apply (zero_unique zx zy); assumption).
      subst zy.
      exact (successor_functional zx x y Hsuccx Hsuccy).
    Qed.
    
    (** Two is the successor of one *)
    Definition IsTwo : AlphaPred := fun x => exists o, IsOne o /\ Succ o x.
    
    (** Key lemma: 1 is not 0 *)
    Lemma one_not_zero : forall o z, IsOne o -> IsZero z -> o <> z.
    Proof.
      intros o z [zo [Hzo Hsucc]] Hz Heq.
      subst o.
      exact (zero_not_successor zo z Hz Hsucc).
    Qed.
    
    (** We axiomatize a specific one element *)
    Axiom one : Alphacarrier.
    Axiom one_is_one : IsOne one.
    Axiom one_is_nat : IsNat one.
    
  End Definitions.
  
End Arithmetic.