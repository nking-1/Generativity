Require Import DAO.Core.OmegaType.

Section OmegaProperties.
  Context {Omega : OmegaType}.
  
  (** Omega contains paradoxes - for any predicate P, there exists an x
      that both satisfies and doesn't satisfy P *)
  Theorem omega_has_paradoxes :
    forall (P : Omegacarrier -> Prop),
    exists x : Omegacarrier, P x /\ ~ P x.
  Proof.
    intro P.
    pose (paradox := fun x => P x /\ ~ P x).
    exact (omega_completeness paradox).
  Qed.
  
  (** Omega has self-referential witnesses - the liar paradox *)
  Theorem omega_has_liar :
    exists x : Omegacarrier,
    exists P : Omegacarrier -> Prop,
    P x <-> ~ P x.
  Proof.
    pose (liar_pred := fun x => 
      exists P : Omegacarrier -> Prop, P x <-> ~ P x).
    destruct (omega_completeness liar_pred) as [x Hx].
    exists x. exact Hx.
  Qed.
  
  (** Omega is non-empty *)
  Theorem omega_not_empty :
    exists x : Omegacarrier, True.
  Proof.
    destruct (omega_completeness (fun _ => True)) as [x _].
    exists x. exact I.
  Qed.

  Theorem omega_completeness_implies_contradiction :
    forall `{H_O: OmegaType},
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y) ->
      exists R: Omegacarrier -> Prop, 
        (exists z: Omegacarrier, R z) /\ (forall z: Omegacarrier, R z -> False).
  Proof.
    intros H_O omega_complete.
    set (R := fun _ : Omegacarrier => False).
    exists R.
    split.
    - apply omega_complete.
    - intros z Hz. exact Hz.
  Qed.

  Theorem contradiction_implies_omega_completeness :
    forall `{H_O: OmegaType},
      (exists R: Omegacarrier -> Prop, 
        (exists z: Omegacarrier, R z) /\ (forall z: Omegacarrier, R z -> False)) ->
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y).
  Proof.
    intros H_O [R [[z Hz] H_uninhab]] Q.
    exfalso.
    exact (H_uninhab z Hz).
  Qed.

  Theorem complete_iff_contradictory :
    forall `{H_O: OmegaType},
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y) <->
      exists R: Omegacarrier -> Prop, 
        (exists z: Omegacarrier, R z) /\ (forall z: Omegacarrier, R z -> False).
  Proof.
    intros H_O.
    split.
    - apply omega_completeness_implies_contradiction.
    - apply contradiction_implies_omega_completeness.
  Qed.
  
  (** From Omega's paradoxes, we can prove anything (triviality) *)
  Theorem omega_proves_anything :
    forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x.
  Proof.
    intros P x.
    destruct (omega_has_paradoxes P) as [w [Hw Hnw]].
    (* We have Hw : P w and Hnw : ~ P w, which is a contradiction *)
    contradiction.
  Qed.
  
End OmegaProperties.
