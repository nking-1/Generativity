Require Import DAO.Core.AlphaType.

(* ============================================================ *)
(* Properties of AlphaType *)  
(* ============================================================ *)

Section AlphaProperties.
  Context {Alpha : AlphaType}.
  
  (** The impossible predicate has no witnesses *)
  Theorem omega_veil_has_no_witnesses :
    forall x : Alphacarrier, ~ omega_veil x.
  Proof.
    intro x.
    unfold omega_veil.
    exact (proj1 (proj2_sig alpha_impossibility) x).
  Qed.
  
  (** The impossible predicate is unique *)
  Theorem omega_veil_unique :
    forall Q : Alphacarrier -> Prop,
    (forall x : Alphacarrier, ~ Q x) ->
    (forall x : Alphacarrier, Q x <-> omega_veil x).
  Proof.
    intros Q HQ.
    unfold omega_veil.
    exact (proj2 (proj2_sig alpha_impossibility) Q HQ).
  Qed.
  
  (** Not all predicates are impossible *)
  Theorem exists_possible_predicate :
    exists P : Alphacarrier -> Prop,
    exists x : Alphacarrier, P x.
  Proof.
    exists (fun _ => True).
    destruct alpha_not_empty as [x _].
    exists x. exact I.
  Qed.
  
End AlphaProperties.
