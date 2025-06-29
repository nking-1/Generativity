Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.

(* TODO: Can we define arithmetic operations or numbers by using omega_veil? *)
(* The axioms here are reasonable, but it's more fun if we construct from the veil directly *)

Section ConstructiveArithmetic.
  Context {Alpha : AlphaType}.
  
  (* Natural numbers as Alpha predicates *)
  Variable IsNat : Alphacarrier -> Prop.
  Variable IsZero : Alphacarrier -> Prop.
  Variable Succ : Alphacarrier -> Alphacarrier -> Prop.
  
  (* Axiom 1: Zero exists and is natural *)
  Axiom zero_exists : exists z, IsZero z /\ IsNat z.
  
  (* Axiom 2: Zero is unique *)
  Axiom zero_unique : forall x y, IsZero x -> IsZero y -> x = y.
  
  (* Axiom 3: Every natural has a successor *)
  Axiom successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y.
  
  (* Axiom 4: Successor is functional *)
  Axiom successor_functional : forall x y z, Succ x y -> Succ x z -> y = z.
  
  (* Axiom 5: No number is its own successor *)
  Axiom no_self_successor : forall x, ~ Succ x x.
  
  (* Axiom 6: Successor is injective *)
  Axiom successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y.
  
  (* Axiom 7: Zero is not a successor *)
  Axiom zero_not_successor : forall x y, IsZero y -> ~ Succ x y.
  
  (* Axiom 8: Induction - this works constructively! *)
  Axiom nat_induction : 
    forall (P : Alphacarrier -> Prop),
      (forall z, IsZero z -> P z) ->
      (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
      (forall n, IsNat n -> P n).
  
  (* Let's prove some basic theorems constructively *)
  
  (* Zero exists as a witness - no excluded middle needed *)
  Theorem zero_witness :
    exists z, IsZero z.
  Proof.
    destruct zero_exists as [z [Hz _]].
    exists z. exact Hz.
  Qed.
  
  (* Natural numbers exist - constructive *)
  Theorem nat_witness :
    exists n, IsNat n.
  Proof.
    destruct zero_exists as [z [_ Hz]].
    exists z. exact Hz.
  Qed.
  
  (* Every natural has a unique successor - constructive *)
  Theorem successor_unique_constructive :
    forall n, IsNat n -> 
    exists s, Succ n s /\ forall s', Succ n s' -> s = s'.
  Proof.
    intros n Hn.
    destruct (successor_exists n Hn) as [s [Hs HsNat]].
    exists s. split.
    - exact Hs.
    - intros s' Hs'.
      exact (successor_functional n s s' Hs Hs').
  Qed.
  
  (* Define One as successor of zero - constructive *)
  Definition IsOne : Alphacarrier -> Prop :=
    fun x => exists z, IsZero z /\ Succ z x.
  
  (* One exists - constructive *)
  Theorem one_exists : exists o, IsOne o.
  Proof.
    destruct zero_exists as [z [Hz HzNat]].
    destruct (successor_exists z HzNat) as [o [Hsucc HoNat]].
    exists o. exists z. split; assumption.
  Qed.
  
  (* Now let's add addition constructively *)
  Variable Plus : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.
  
  (* Addition axioms - all constructive *)
  Axiom plus_zero_right : forall x z, IsZero z -> IsNat x -> Plus x z x.
  Axiom plus_successor : forall x y z sx sy sz,
    IsNat x -> IsNat y -> IsNat z ->
    Succ x sx -> Succ y sy -> Succ z sz ->
    Plus x y z -> Plus sx y sz.
  Axiom plus_functional : forall x y z1 z2,
    Plus x y z1 -> Plus x y z2 -> z1 = z2.
  Axiom plus_total : forall x y,
    IsNat x -> IsNat y -> exists z, IsNat z /\ Plus x y z.
  
  (* We can define addition recursively - constructive *)
  Theorem plus_computable :
    forall x y, IsNat x -> IsNat y ->
    exists! z, Plus x y z.
  Proof.
    intros x y Hx Hy.
    destruct (plus_total x y Hx Hy) as [z [Hz HPl]].
    exists z. split.
    - exact HPl.
    - intros z' HPl'.
      exact (plus_functional x y z z' HPl HPl').
  Qed.
  
  (* Similarly for multiplication *)
  Variable Times : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.
  
  Axiom times_zero_right : forall x z, IsZero z -> IsNat x -> Times x z z.
  Axiom times_successor : forall x y z xy sxy,
    IsNat x -> IsNat y -> IsNat z ->
    Succ y z ->
    Times x y xy -> Plus xy x sxy ->
    Times x z sxy.
  Axiom times_total : forall x y,
    IsNat x -> IsNat y -> exists z, IsNat z /\ Times x y z.
  
  (* The key theorem: arithmetic is decidable in our constructive system *)
  (* This is crucial for Gödel's theorem to apply *)
  
  (* Define what it means to be a successor *)
  Definition IsSuccessor (n : Alphacarrier) : Type :=
    sigT (fun m : Alphacarrier => IsNat m /\ Succ m n).
  
  (* Now the axiom using explicit sum *)
  Axiom zero_or_successor_dec : forall n, IsNat n -> 
    sum (IsZero n) (IsSuccessor n).
  
  (* Helper lemma for decidable equality at zero *)
  Lemma eq_zero_dec : forall x, IsNat x -> IsZero x ->
    forall y, IsNat y -> {x = y} + {x <> y}.
  Proof.
    intros x Hx Hx0 y Hy.
    destruct (zero_or_successor_dec y Hy) as [Hy0 | Hsucc].
    - left. exact (zero_unique x y Hx0 Hy0).
    - right. intro H. subst x.  (* More explicit: subst x with y *)
      destruct Hsucc as [y' [Hy' Hsy']].
      exact (zero_not_successor y' y Hx0 Hsy').
  Defined.

  (* axiom for Type-valued induction *)
  Axiom nat_induction_Type : 
    forall (P : Alphacarrier -> Type),
      (forall z, IsZero z -> IsNat z -> P z) ->  (* Added IsNat z here *)
      (forall n m, IsNat n -> P n -> Succ n m -> IsNat m -> P m) ->  (* Added IsNat m *)
      (forall n, IsNat n -> P n).
  
  Definition nat_eq_dec : forall x y, IsNat x -> IsNat y ->
    {x = y} + {x <> y}.
  Proof.
    intros x y Hx Hy.
    (* Induct on x *)
    revert y Hy.
    apply (nat_induction_Type (fun x => forall y, IsNat y -> {x = y} + {x <> y})).
    
    - (* Base case: x is zero *)
      intros z Hz HzNat.
      exact (eq_zero_dec z HzNat Hz).
      
    - (* Inductive case: x = successor of n *)
      intros n m Hn IH Hsucc HmNat y Hy.
      destruct (zero_or_successor_dec y Hy) as [Hy0 | Hsucc_y].
      + (* y is zero, m is successor *)
        right. intro H. subst.
        exact (zero_not_successor n y Hy0 Hsucc).
      + (* both are successors *)
        destruct Hsucc_y as [y' [Hy' Hsy']].
        destruct (IH y' Hy') as [Heq | Hneq].
        * (* predecessors equal *)
          left. subst.
          exact (successor_functional y' m y Hsucc Hsy').
        * (* predecessors not equal *)
          right. intro H. apply Hneq.
          exact (successor_injective n y' m Hn Hy' Hsucc (eq_ind_r (fun z => Succ y' z) Hsy' H)).
    
    - (* Apply to x *)
      exact Hx.
  Defined.
  
  (* Primality can be defined constructively *)
  Definition Divides (d n : Alphacarrier) : Prop :=
    exists q, IsNat q /\ Times d q n.
  
  Definition IsPrime (p : Alphacarrier) : Prop :=
    IsNat p /\
    ~ IsZero p /\
    ~ IsOne p /\
    forall d, IsNat d -> Divides d p -> IsOne d \/ d = p.
  
End ConstructiveArithmetic.
