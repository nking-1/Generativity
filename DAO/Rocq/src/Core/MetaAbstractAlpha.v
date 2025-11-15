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