(** AlphaFirewall.v
    Paradox firewalls in AlphaType. AlphaType prevents various paradoxes by making them collapse to omega_veil.
    This is a good file to add more "Red Teaming" theorems to test the integrity of the system later. *)
Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.


Section AlphaParadoxFirewalls.
  Context {Alpha : AlphaType}.
  
  (** Russell's Paradox cannot exist in Alpha *)
  Theorem alpha_no_russell_predicate :
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
  Theorem alpha_no_curry_false :
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
  Theorem alpha_curry_explosion :
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
  Theorem alpha_no_self_denying :
    ~ exists (P : Alphacarrier -> Prop),
      (forall x, P x <-> omega_veil x) /\ (exists x, P x).
  Proof.
    intros [P [Heq [x Px]]].
    apply (AlphaProperties.Core.omega_veil_has_no_witnesses x).
    apply Heq. exact Px.
  Qed.

  Definition alpha_circular_predicate (P : Alphacarrier -> Prop) : Prop :=
    forall x, P x <-> exists y, P y.
  
  (* If a circular predicate has a witness, it's universal *)
  Theorem alpha_circular_witness_universal :
    forall P : Alphacarrier -> Prop,
      alpha_circular_predicate P ->
      (exists x, P x) ->
      forall y, P y.
  Proof.
    intros P Hcirc [x Px] y.
    apply Hcirc.
    exists x. exact Px.
  Qed.
  
  (* And if it's not universal, it has no witnesses *)
  Theorem alpha_circular_not_universal_empty :
    forall P : Alphacarrier -> Prop,
      alpha_circular_predicate P ->
      (exists y, ~ P y) ->
      forall x, ~ P x.
  Proof.
    intros P Hcirc [y HnPy] x Px.
    apply HnPy.
    apply Hcirc.
    exists x. exact Px.
  Qed.
  
  (* Circular predicates can't be "mixed" *)
  Theorem alpha_circular_no_mixed :
    forall P : Alphacarrier -> Prop,
      alpha_circular_predicate P ->
      ~ ((exists x, P x) /\ (exists y, ~ P y)).
  Proof.
    intros P Hcirc [[x Px] [y HnPy]].
    apply HnPy.
    apply (alpha_circular_witness_universal P Hcirc).
    - exists x. exact Px.
  Qed.
  
End AlphaParadoxFirewalls.

Section ParadoxesEqualTheImpossible.
  Context {Alpha : AlphaType}.
  
  (* First, let's prove that any predicate that always leads to False 
     must equal omega_veil *)
  Theorem alpha_contradiction_equals_impossible :
    forall P : Alphacarrier -> Prop,
    (forall x : Alphacarrier, P x -> False) ->
    (forall x : Alphacarrier, P x <-> omega_veil x).
  Proof.
    intros P HP.
    apply AlphaProperties.Core.omega_veil_unique.
    intros x Px.
    exact (HP x Px).
  Qed.
  
  (* Now let's show Russell's paradox equals omega_veil *)
  Theorem alpha_russell_equals_impossible :
    forall R : Alphacarrier -> Prop,
    (forall x, R x <-> ~ R x) ->
    (forall x, R x <-> omega_veil x).
  Proof.
    intros R HR.
    apply alpha_contradiction_equals_impossible.
    intros x Rx.
    (* R x -> ~ R x by HR *)
    apply (proj1 (HR x) Rx).
    exact Rx.
  Qed.
  
  (* Curry's paradox with False equals omega_veil *)
  Theorem alpha_curry_false_equals_impossible :
    forall C : Alphacarrier -> Prop,
    (forall x, C x <-> (C x -> False)) ->
    (forall x, C x <-> omega_veil x).
  Proof.
    intros C HC.
    apply alpha_contradiction_equals_impossible.
    intros x Cx.
    (* C x -> (C x -> False) by HC *)
    apply (proj1 (HC x) Cx).
    exact Cx.
  Qed.
  
  (* Here's a more general principle: any self-contradictory predicate
     equals omega_veil *)
  Theorem alpha_self_contradictory_equals_impossible :
    forall P : Alphacarrier -> Prop,
    (exists x, P x -> ~ P x) ->
    (forall x, ~ P x) ->
    (forall x, P x <-> omega_veil x).
  Proof.
    intros P Hself Hnone.
    apply AlphaProperties.Core.omega_veil_unique.
    exact Hnone.
  Qed.
  
  (* Even more interesting: predicates that would make everything true
     must be impossible *)
  Theorem alpha_trivializing_equals_impossible :
    forall P : Alphacarrier -> Prop,
    (forall Q : Prop, (exists x, P x) -> Q) ->
    (forall x, P x <-> omega_veil x).
  Proof.
    intros P Htriv.
    apply alpha_contradiction_equals_impossible.
    intros x Px.
    (* If P x, then we can prove False *)
    apply (Htriv False).
    exists x. exact Px.
  Qed.
  
  (* The circular predicate, if it has no witnesses, equals omega_veil *)
  Theorem alpha_empty_circular_equals_impossible :
    forall P : Alphacarrier -> Prop,
    alpha_circular_predicate P ->
    (forall x, ~ P x) ->
    (forall x, P x <-> omega_veil x).
  Proof.
    intros P Hcirc Hempty.
    apply AlphaProperties.Core.omega_veil_unique.
    exact Hempty.
  Qed.
  
  (* The key theorem: In AlphaType, all paradoxes are the same paradox *)
  Theorem alpha_all_paradoxes_are_one :
    forall P Q : Alphacarrier -> Prop,
    (forall x, ~ P x) ->
    (forall x, ~ Q x) ->
    (forall x, P x <-> Q x).
  Proof.
    intros P Q HP HQ x.
    split.
    - intro Px. destruct (HP x Px).
    - intro Qx. destruct (HQ x Qx).
  Qed.
  
  (* Therefore: there's only one way to be impossible in AlphaType *)
  Theorem alpha_impossibility_is_unique :
    forall P : Alphacarrier -> Prop,
    (forall x, ~ P x) <->
    (forall x, P x <-> omega_veil x).
  Proof.
    intro P.
    split.
    - apply AlphaProperties.Core.omega_veil_unique.
    - intros H x Px.
      apply (AlphaProperties.Core.omega_veil_has_no_witnesses x).
      apply H. exact Px.
  Qed.

End ParadoxesEqualTheImpossible.