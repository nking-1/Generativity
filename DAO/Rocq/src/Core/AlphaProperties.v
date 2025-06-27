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

(** ** Paradox Firewalls in AlphaType
    
    AlphaType prevents various paradoxes by making them collapse to omega_veil *)

Section ParadoxFirewalls.
  Context {Alpha : AlphaType}.
  
  (** Russell's Paradox cannot exist in Alpha *)
  Theorem no_russell_predicate :
    ~ exists (R : Alphacarrier -> Prop), 
      forall x, R x <-> ~ R x.
  Proof.
    intros [R HR].
    destruct alpha_not_empty as [x0 _].
    specialize (HR x0).
    destruct HR as [H1 H2].
    assert (R x0 -> False).
    { intro Hr. apply (H1 Hr). exact Hr. }
    apply H. apply H2. exact H.
  Qed.
  
  (** Curry's Paradox for False cannot exist *)
  Theorem no_curry_false :
    ~ exists (C : Alphacarrier -> Prop),
      forall x, C x <-> (C x -> False).
  Proof.
    intros [C HC].
    destruct alpha_not_empty as [x0 _].
    specialize (HC x0).
    destruct HC as [H1 H2].
    
    assert (HnC: ~ C x0).
    { intros HC0.
      apply (H1 HC0). exact HC0. }
    
    apply HnC. apply H2. exact HnC.
  Qed.
  
  (** General Curry's Paradox: if such a predicate exists, Q becomes provable *)
  Theorem curry_explosion :
    forall (Q : Prop),
      (exists (C : Alphacarrier -> Prop), forall x, C x <-> (C x -> Q)) -> 
      Q.
  Proof.
    intros Q [C HC].
    destruct alpha_not_empty as [x0 _].
    specialize (HC x0).
    destruct HC as [H1 H2].
    
    assert (HQ: (C x0 -> Q) -> Q).
    { intros Himp.
      apply Himp. apply H2. exact Himp. }
    
    apply HQ.
    intros HC0.
    apply HQ.
    apply H1.
    exact HC0.
  Qed.
  
  (** No predicate can be both omega_veil and have a witness *)
  Theorem no_self_denying :
    ~ exists (P : Alphacarrier -> Prop),
      (forall x, P x <-> omega_veil x) /\ (exists x, P x).
  Proof.
    intros [P [Heq [x Px]]].
    apply (omega_veil_has_no_witnesses x).
    apply Heq. exact Px.
  Qed.

  Definition circular_predicate (P : Alphacarrier -> Prop) : Prop :=
    forall x, P x <-> exists y, P y.
  
  (* If a circular predicate has a witness, it's universal *)
  Theorem circular_witness_universal :
    forall P : Alphacarrier -> Prop,
      circular_predicate P ->
      (exists x, P x) ->
      forall y, P y.
  Proof.
    intros P Hcirc [x Px] y.
    apply Hcirc.
    exists x. exact Px.
  Qed.
  
  (* And if it's not universal, it has no witnesses *)
  Theorem circular_not_universal_empty :
    forall P : Alphacarrier -> Prop,
      circular_predicate P ->
      (exists y, ~ P y) ->
      forall x, ~ P x.
  Proof.
    intros P Hcirc [y HnPy] x Px.
    apply HnPy.
    apply Hcirc.
    exists x. exact Px.
  Qed.
  
  (* Circular predicates can't be "mixed" *)
  Theorem circular_no_mixed :
    forall P : Alphacarrier -> Prop,
      circular_predicate P ->
      ~ ((exists x, P x) /\ (exists y, ~ P y)).
  Proof.
    intros P Hcirc [[x Px] [y HnPy]].
    apply HnPy.
    apply (circular_witness_universal P Hcirc).
    - exists x. exact Px.
  Qed.
  
End ParadoxFirewalls.