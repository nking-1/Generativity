Require Import DAO.Core.AlphaType.

(** * Properties of AlphaType
    
    This module explores the properties of AlphaType, particularly
    the omega_veil predicate and its uniqueness. *)

Module AlphaProperties.

  (** ** Core Properties
      
      Basic properties of the omega_veil predicate *)
  Module Core.
    
    (** The impossible predicate has no witnesses *)
    Theorem omega_veil_has_no_witnesses {Alpha : AlphaType} :
      forall x : Alphacarrier, ~ omega_veil x.
    Proof.
      intro x.
      unfold omega_veil.
      exact (proj1 (proj2_sig alpha_impossibility) x).
    Qed.
    
    (** The impossible predicate is unique *)
    Theorem omega_veil_unique {Alpha : AlphaType} :
      forall Q : Alphacarrier -> Prop,
      (forall x : Alphacarrier, ~ Q x) ->
      (forall x : Alphacarrier, Q x <-> omega_veil x).
    Proof.
      intros Q HQ.
      unfold omega_veil.
      exact (proj2 (proj2_sig alpha_impossibility) Q HQ).
    Qed.
    
  End Core.

  (** ** Existence Properties
      
      Properties about what exists in Alpha *)
  Module Existence.
    
    (** Not all predicates are impossible *)
    Theorem exists_possible_predicate {Alpha : AlphaType} :
      exists P : Alphacarrier -> Prop,
      exists x : Alphacarrier, P x.
    Proof.
      exists (fun _ => True).
      destruct alpha_not_empty as [x _].
      exists x. exact I.
    Qed.
    
  End Existence.

End AlphaProperties.