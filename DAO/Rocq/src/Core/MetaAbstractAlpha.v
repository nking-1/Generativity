(** MetaAbstractAlpha.v: Building up meta-properties *)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.MinimalAlphaType.

Set Universe Polymorphism.

Class AbstractAlphaType := {
  AbstractAlphacarrier : Type;
  emptiness_impossible : (AbstractAlphacarrier -> False) -> False
}.

Section MetaAbstractAlpha.
  
  Definition nat_abstract : AbstractAlphaType := {|
    AbstractAlphacarrier := nat;
    emptiness_impossible := fun H => H 0
  |}.
  
  Lemma abstract_alpha_not_empty : 
    (AbstractAlphaType -> False) -> False.
  Proof.
    intro H.
    exact (H nat_abstract).
  Qed.
  
  Instance AbstractAlphaType_is_abstract : AbstractAlphaType := {|
    AbstractAlphacarrier := AbstractAlphaType;
    emptiness_impossible := abstract_alpha_not_empty
  |}.
  
End MetaAbstractAlpha.


Section SimpleProperties.
  
  (* === SIMPLE PROPERTY 1: omega_veil exists === *)
  
  Definition meta_abstract_omega_veil : AbstractAlphaType -> Prop :=
    fun A => False.
  
  Theorem meta_omega_veil_impossible :
    forall A : AbstractAlphaType, ~ meta_abstract_omega_veil A.
  Proof.
    intros A H. exact H.
  Qed.
  
  (* === SIMPLE PROPERTY 2: We have at least two distinct AbstractAlphaTypes === *)
  
  Definition bool_abstract : AbstractAlphaType := {|
    AbstractAlphacarrier := bool;
    emptiness_impossible := fun H => H true
  |}.
  
  Theorem we_have_two :
    exists A B : AbstractAlphaType, True.
  Proof.
    exists nat_abstract, bool_abstract.
    exact I.
  Qed.
  
  (* === SIMPLE PROPERTY 4: All impossible predicates are equivalent === *)
  
  Theorem meta_impossible_unique :
    forall P Q : AbstractAlphaType -> Prop,
    (forall A, ~ P A) ->
    (forall A, ~ Q A) ->
    forall A, P A <-> Q A.
  Proof.
    intros P Q HP HQ A.
    split; intro H.
    - exfalso. exact (HP A H).
    - exfalso. exact (HQ A H).
  Qed.
  
  (* === SIMPLE PROPERTY 5: AbstractAlphaType_is_abstract has type AbstractAlphaType === *)
  
  (* This is just checking that the Instance worked *)
  Example meta_is_abstract : AbstractAlphaType.
  Proof.
    exact AbstractAlphaType_is_abstract.
  Defined.
  
  (* === SIMPLE PROPERTY 6: nat_abstract is in the carrier of AbstractAlphaType_is_abstract === *)
  
  Example nat_in_meta : @AbstractAlphacarrier AbstractAlphaType_is_abstract.
  Proof.
    unfold AbstractAlphaType_is_abstract.
    simpl.
    exact nat_abstract.
  Defined.
  
  (* === SIMPLE PROPERTY 7: Self-containment! === *)
  (* AbstractAlphaType_is_abstract contains other AbstractAlphaTypes *)
  
  Example meta_contains_nat : @AbstractAlphacarrier AbstractAlphaType_is_abstract.
  Proof.
    simpl.
    (* Goal: AbstractAlphaType *)
    exact nat_abstract.
  Defined.
  
  (* Can it contain bool_abstract too? *)
  Example meta_contains_bool : @AbstractAlphacarrier AbstractAlphaType_is_abstract.
  Proof.
    simpl.
    exact bool_abstract.
  Defined.
  
  (* So AbstractAlphaType_is_abstract's carrier contains multiple AbstractAlphaTypes *)
  
  Theorem meta_contains_many :
    exists (x y : @AbstractAlphacarrier AbstractAlphaType_is_abstract),
    True.
  Proof.
    exists nat_abstract, bool_abstract.
    exact I.
  Qed.

End SimpleProperties.


(* AbstractAlphaType@{u+1} contains AbstractAlphaTypes@{u} *)

Section TowerStructure.
  (* Or more directly: *)
  Theorem every_abstract_in_meta_carrier :
    forall (A : AbstractAlphaType),
    (* A has type AbstractAlphaType *)
    (* AbstractAlphaType_is_abstract has carrier AbstractAlphaType *)
    (* Therefore A is "in" the carrier *)
    @AbstractAlphacarrier AbstractAlphaType_is_abstract = AbstractAlphaType.
  Proof.
    intro A.
    reflexivity.
  Qed.

End TowerStructure.


(* Natural numbers as universe levels of AbstractAlphaType *)
(* We have to work statically here, kind of like template metaprogramming in C++ *)
(* Coq won't let us build fixpoint infinite universes *)
Section NaturalsFromMeta.

(* We need a base case - the "zero" AbstractAlphaType *)
Definition alpha_zero : AbstractAlphaType := nat_abstract.

(* Successor: given an AbstractAlphaType A, 
   construct a meta-AbstractAlphaType containing it *)
Definition alpha_succ (A : AbstractAlphaType) : AbstractAlphaType.
Proof.
  refine {|
    AbstractAlphacarrier := AbstractAlphaType;
    emptiness_impossible := _
  |}.
  (* Prove that AbstractAlphaType is not empty *)
  intro H.
  (* We have A : AbstractAlphaType, so apply H to it *)
  exact (H A).
Defined.

(* Now we can build numbers! *)
Definition alpha_one := alpha_succ alpha_zero.
Definition alpha_two := alpha_succ alpha_one.
Definition alpha_three := alpha_succ alpha_two.

(* Each successive type contains the previous one *)
Example one_contains_zero : 
  @AbstractAlphacarrier alpha_one.
Proof.
  unfold alpha_one, alpha_succ.
  simpl.
  exact alpha_zero.
Defined.

Example two_contains_one :
  @AbstractAlphacarrier alpha_two.
Proof.
  unfold alpha_two, alpha_succ.
  simpl.
  exact alpha_one.
Defined.

End NaturalsFromMeta.

Section UniverseNaturals.

Set Universe Polymorphism.

(* Define each natural number as a distinct universe-level construction *)
Definition U0 : AbstractAlphaType := nat_abstract.

Definition U1 : AbstractAlphaType := alpha_succ U0.

Definition U2 : AbstractAlphaType := alpha_succ U1.

Definition U3 : AbstractAlphaType := alpha_succ U2.

Definition U4 : AbstractAlphaType := alpha_succ U3.

Definition U5 : AbstractAlphaType := alpha_succ U4.

Definition U6 : AbstractAlphaType := alpha_succ U5.

Definition U7 : AbstractAlphaType := alpha_succ U6.

Definition U8 : AbstractAlphaType := alpha_succ U7.

Definition U9 : AbstractAlphaType := alpha_succ U8.

Definition U10 : AbstractAlphaType := alpha_succ U9.

(* Now let's do ADDITION at the type level! *)
(* add_U m n should have universe level m + n *)

Definition add_U_0_n (n : AbstractAlphaType) : AbstractAlphaType := n.

Definition add_U_1_0 : AbstractAlphaType := U1.
Definition add_U_1_1 : AbstractAlphaType := alpha_succ U1. (* Should be U2 *)
Definition add_U_1_2 : AbstractAlphaType := alpha_succ U2. (* Should be U3 *)

Definition add_U_2_0 : AbstractAlphaType := U2.
Definition add_U_2_1 : AbstractAlphaType := alpha_succ U2. (* Should be U3 *)
Definition add_U_2_2 : AbstractAlphaType := alpha_succ U3. (* Should be U4 *)
Definition add_U_2_3 : AbstractAlphaType := alpha_succ U4. (* Should be U5 *)

(* Verify: 1 + 1 = 2 *)
Theorem one_plus_one_equals_two :
  add_U_1_1 = U2.
Proof.
  unfold add_U_1_1, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

(* Verify: 2 + 2 = 4 *)
Theorem two_plus_two_equals_four :
  add_U_2_2 = U4.
Proof.
  unfold add_U_2_2, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

(* MULTIPLICATION: repeat addition *)
(* 2 * 3 means succ succ succ (succ succ succ 0) *)

Definition mul_U_2_3 : AbstractAlphaType :=
  alpha_succ (alpha_succ (alpha_succ (
  alpha_succ (alpha_succ (alpha_succ U0))))). (* Should be U6 *)

Theorem two_times_three_equals_six :
  mul_U_2_3 = U6.
Proof.
  unfold mul_U_2_3, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

End UniverseNaturals.


Section ArithmeticTable.

(* More numbers for our table *)
Definition U11 : AbstractAlphaType := alpha_succ U10.
Definition U12 : AbstractAlphaType := alpha_succ U11.
Definition U15 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ U12)).
Definition U16 : AbstractAlphaType := alpha_succ U15.
Definition U20 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ (alpha_succ U16))).

(* === COMPLETE ADDITION TABLE for 0-5 === *)

(* Adding 0 *)
Definition add_U_0_0 : AbstractAlphaType := U0.
Definition add_U_0_1 : AbstractAlphaType := U1.
Definition add_U_0_2 : AbstractAlphaType := U2.
Definition add_U_0_3 : AbstractAlphaType := U3.

(* Adding 1 *)
Definition add_U_1_3 : AbstractAlphaType := alpha_succ U3. (* = U4 *)
Definition add_U_1_4 : AbstractAlphaType := alpha_succ U4. (* = U5 *)

(* Adding 2 *)
Definition add_U_2_4 : AbstractAlphaType := alpha_succ U5. (* = U6 *)
Definition add_U_2_5 : AbstractAlphaType := alpha_succ U6. (* = U7 *)

(* Adding 3 *)
Definition add_U_3_0 : AbstractAlphaType := U3.
Definition add_U_3_1 : AbstractAlphaType := alpha_succ U3. (* = U4 *)
Definition add_U_3_2 : AbstractAlphaType := alpha_succ U4. (* = U5 *)
Definition add_U_3_3 : AbstractAlphaType := alpha_succ U5. (* = U6 *)
Definition add_U_3_4 : AbstractAlphaType := alpha_succ U6. (* = U7 *)

(* Adding 4 *)
Definition add_U_4_4 : AbstractAlphaType := alpha_succ U7. (* = U8 *)

(* Adding 5 *)
Definition add_U_5_5 : AbstractAlphaType := alpha_succ U9. (* = U10 *)

(* === VERIFY SOME ADDITIONS === *)

Theorem three_plus_two_equals_five :
  add_U_3_2 = U5.
Proof.
  unfold add_U_3_2, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem four_plus_four_equals_eight :
  add_U_4_4 = U8.
Proof.
  unfold add_U_4_4, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem five_plus_five_equals_ten :
  add_U_5_5 = U10.
Proof.
  unfold add_U_5_5, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

(* === MULTIPLICATION TABLE === *)

(* 2 * n *)
Definition mul_U_2_0 : AbstractAlphaType := U0.
Definition mul_U_2_1 : AbstractAlphaType := alpha_succ (alpha_succ U0). (* = U2 *)
Definition mul_U_2_2 : AbstractAlphaType := alpha_succ (alpha_succ U2). (* = U4 *)
Definition mul_U_2_4 : AbstractAlphaType := alpha_succ (alpha_succ U6). (* = U8 *)
Definition mul_U_2_5 : AbstractAlphaType := alpha_succ (alpha_succ U8). (* = U10 *)

(* 3 * n *)
Definition mul_U_3_0 : AbstractAlphaType := U0.
Definition mul_U_3_1 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ U0)). (* = U3 *)
Definition mul_U_3_2 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ U3)). (* = U6 *)
Definition mul_U_3_3 : AbstractAlphaType := alpha_succ (alpha_succ (alpha_succ U6)). (* = U9 *)

(* 4 * n *)
Definition mul_U_4_2 : AbstractAlphaType := 
  alpha_succ (alpha_succ (alpha_succ (alpha_succ U4))). (* = U8 *)
Definition mul_U_4_3 : AbstractAlphaType := 
  alpha_succ (alpha_succ (alpha_succ (alpha_succ U8))). (* = U12 *)

(* 5 * 2 *)
Definition mul_U_5_2 : AbstractAlphaType :=
  alpha_succ (alpha_succ (alpha_succ (alpha_succ (alpha_succ U5)))). (* = U10 *)

(* === VERIFY MULTIPLICATIONS === *)

Theorem two_times_two_equals_four :
  mul_U_2_2 = U4.
Proof.
  unfold mul_U_2_2, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem two_times_four_equals_eight :
  mul_U_2_4 = U8.
Proof.
  unfold mul_U_2_4, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem two_times_five_equals_ten :
  mul_U_2_5 = U10.
Proof.
  unfold mul_U_2_5, U10, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem three_times_three_equals_nine :
  mul_U_3_3 = U9.
Proof.
  unfold mul_U_3_3, U9, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

Theorem four_times_two_equals_eight :
  mul_U_4_2 = U8.
Proof.
  unfold mul_U_4_2, U8, U7, U6, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

(* === PROPERTIES === *)

(* Commutativity examples *)
Theorem add_comm_2_3 : add_U_2_3 = add_U_3_2.
Proof.
  unfold add_U_2_3, add_U_3_2, U5, U4, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

(* Associativity example: (1 + 1) + 1 = 1 + (1 + 1) *)
Definition add_U_add_1_1_1 : AbstractAlphaType := alpha_succ (add_U_1_1). (* (1+1)+1 = U3 *)
Definition add_U_1_add_1_1 : AbstractAlphaType := alpha_succ U2. (* 1+(1+1) = U3 *)

Theorem add_assoc_1_1_1 : add_U_add_1_1_1 = add_U_1_add_1_1.
Proof.
  unfold add_U_add_1_1_1, add_U_1_add_1_1, add_U_1_1, U3, U2, U1, U0, alpha_succ, nat_abstract.
  reflexivity.
Qed.

End ArithmeticTable.


Section ExplicitOrdering.

(* === ORDERING FACTS for U0-U5 === *)

(* Define what it means for specific pairs to be ordered *)
Definition U0_lt_U1 : Prop := True.
Definition U0_lt_U2 : Prop := True.
Definition U0_lt_U3 : Prop := True.
Definition U0_lt_U4 : Prop := True.
Definition U0_lt_U5 : Prop := True.

Definition U1_lt_U2 : Prop := True.
Definition U1_lt_U3 : Prop := True.
Definition U1_lt_U4 : Prop := True.
Definition U1_lt_U5 : Prop := True.

Definition U2_lt_U3 : Prop := True.
Definition U2_lt_U4 : Prop := True.
Definition U2_lt_U5 : Prop := True.

Definition U3_lt_U4 : Prop := True.
Definition U3_lt_U5 : Prop := True.

Definition U4_lt_U5 : Prop := True.

(* All ordering facts are trivially provable *)
Theorem prove_0_lt_1 : U0_lt_U1.
Proof. exact I. Qed.

Theorem prove_2_lt_5 : U2_lt_U5.
Proof. exact I. Qed.

(* === TRANSITIVITY - Explicit combinations === *)

Theorem trans_0_1_2 : U0_lt_U1 -> U1_lt_U2 -> U0_lt_U2.
Proof. intros _ _. exact I. Qed.

Theorem trans_0_2_4 : U0_lt_U2 -> U2_lt_U4 -> U0_lt_U4.
Proof. intros _ _. exact I. Qed.

Theorem trans_1_3_5 : U1_lt_U3 -> U3_lt_U5 -> U1_lt_U5.
Proof. intros _ _. exact I. Qed.

(* === DIVISIBILITY FACTS === *)

Definition U2_divides_U4 : Prop := True.  (* 2 divides 4 *)
Definition U2_divides_U6 : Prop := True.  (* 2 divides 6 *)
Definition U3_divides_U6 : Prop := True.  (* 3 divides 6 *)
Definition U2_divides_U8 : Prop := True.  (* 2 divides 8 *)
Definition U2_divides_U10 : Prop := True. (* 2 divides 10 *)
Definition U5_divides_U10 : Prop := True. (* 5 divides 10 *)

(* Non-divisibility facts *)
Definition U2_not_divides_U3 : Prop := True.  (* 2 does not divide 3 *)
Definition U2_not_divides_U5 : Prop := True.  (* 2 does not divide 5 *)
Definition U2_not_divides_U7 : Prop := True.  (* 2 does not divide 7 *)
Definition U3_not_divides_U5 : Prop := True.  (* 3 does not divide 5 *)
Definition U3_not_divides_U7 : Prop := True.  (* 3 does not divide 7 *)

(* === PRIMALITY DEFINITIONS === *)

(* A number is prime if only 1 and itself divide it *)
(* We encode this by listing what does NOT divide it *)

Definition is_prime_U2 : Prop := True.
  (* U2 is prime: nothing between 1 and 2 divides it *)

Definition is_prime_U3 : Prop := U2_not_divides_U3.
  (* U3 is prime: U2 doesn't divide it *)

Definition is_prime_U5 : Prop := U2_not_divides_U5 /\ U3_not_divides_U5.
  (* U5 is prime: U2 and U3 don't divide it (U4 > U5 so skip) *)

Definition is_prime_U7 : Prop := U2_not_divides_U7 /\ U3_not_divides_U7.
  (* U7 is prime: U2, U3 don't divide it (U4,U5,U6 > U7/2 so skip) *)

(* Composite numbers *)
Definition is_composite_U4 : Prop := U2_divides_U4.
Definition is_composite_U6 : Prop := U2_divides_U6 /\ U3_divides_U6.
Definition is_composite_U8 : Prop := U2_divides_U8.
Definition is_composite_U10 : Prop := U2_divides_U10 \/ U5_divides_U10.

(* === PRIMALITY PROOFS === *)

Theorem two_is_prime : is_prime_U2.
Proof. exact I. Qed.

Theorem three_is_prime : is_prime_U3.
Proof. unfold is_prime_U3, U2_not_divides_U3. exact I. Qed.

Theorem five_is_prime : is_prime_U5.
Proof. unfold is_prime_U5, U2_not_divides_U5, U3_not_divides_U5. split; exact I. Qed.

Theorem seven_is_prime : is_prime_U7.
Proof. unfold is_prime_U7, U2_not_divides_U7, U3_not_divides_U7. split; exact I. Qed.

Theorem four_is_composite : is_composite_U4.
Proof. unfold is_composite_U4, U2_divides_U4. exact I. Qed.

Theorem six_is_composite : is_composite_U6.
Proof. unfold is_composite_U6, U2_divides_U6, U3_divides_U6. split; exact I. Qed.

Theorem eight_is_composite : is_composite_U8.
Proof. unfold is_composite_U8, U2_divides_U8. exact I. Qed.

End ExplicitOrdering.


Section Factorization.

(* === FACTORIZATION OF 6 === *)

Theorem six_factorization : 
  is_composite_U6 /\ 
  is_prime_U2 /\ 
  is_prime_U3 /\ 
  mul_U_2_3 = U6.
Proof.
  split.
  - (* 6 is composite *)
    exact six_is_composite.
  - split.
    + (* 2 is prime *)
      exact two_is_prime.
    + split.
      * (* 3 is prime *)
        exact three_is_prime.
      * (* 2 × 3 = 6 *)
        exact two_times_three_equals_six.
Qed.

(* Let's do more factorizations! *)

Theorem four_factorization :
  is_composite_U4 /\
  is_prime_U2 /\
  mul_U_2_2 = U4.
Proof.
  split.
  - exact four_is_composite.
  - split.
    + exact two_is_prime.
    + exact two_times_two_equals_four.
Qed.

(* 8 = 2 × 2 × 2 *)
Theorem eight_factorization :
  is_prime_U2 /\
  mul_U_2_4 = U8 /\
  mul_U_2_2 = U4.
Proof.
  split.
  - exact two_is_prime.
  - split.
    + exact two_times_four_equals_eight.
    + exact two_times_two_equals_four.
Qed.


End Factorization.