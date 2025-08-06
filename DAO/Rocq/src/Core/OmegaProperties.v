(** OmegaProperties.v
    Explores the logical consequences of Omega's completeness axiom,
    showing how it leads to paradoxes, contradictions, and logical triviality.
*)

Require Import DAO.Core.OmegaType.

Module OmegaProperties.

  Module Core.
    
    (** Omega is non-empty *)
    Theorem omega_not_empty {Omega : OmegaType} :
      exists x : Omegacarrier, True.
    Proof.
      destruct (omega_completeness (fun _ => True)) as [x _].
      exists x. exact I.
    Qed.
    
    (** Direct consequence: False has a witness (explosion) *)
    Theorem omega_ex_falso {Omega : OmegaType} : False.
    Proof.
      destruct (omega_completeness (fun _ => False)) as [x Hx].
      exact Hx.
    Qed.
    
  End Core.

  Module Paradoxes.
    
    (** For any predicate P, there exists an x that both satisfies and doesn't satisfy P *)
    Theorem omega_has_paradoxes {Omega : OmegaType} :
      forall (P : Omegacarrier -> Prop),
      exists x : Omegacarrier, P x /\ ~ P x.
    Proof.
      intro P.
      pose (paradox := fun x => P x /\ ~ P x).
      exact (omega_completeness paradox).
    Qed.
    
    (** The liar paradox: there exists a self-referential contradiction *)
    Theorem omega_has_liar {Omega : OmegaType} :
      exists x : Omegacarrier,
      exists P : Omegacarrier -> Prop,
      P x <-> ~ P x.
    Proof.
      pose (liar_pred := fun x => 
        exists P : Omegacarrier -> Prop, P x <-> ~ P x).
      destruct (omega_completeness liar_pred) as [x Hx].
      exists x. exact Hx.
    Qed.
    
    (** Russell's paradox variant *)
    Theorem omega_has_russell {Omega : OmegaType} :
      exists x : Omegacarrier,
      exists S : Omegacarrier -> Prop,
      S x <-> (forall P : Omegacarrier -> Prop, P x -> ~ P x).
    Proof.
      pose (russell_pred := fun x =>
        exists S : Omegacarrier -> Prop,
        S x <-> (forall P : Omegacarrier -> Prop, P x -> ~ P x)).
      destruct (omega_completeness russell_pred) as [x Hx].
      exists x. exact Hx.
    Qed.
    
  End Paradoxes.

  Module Triviality.
    Import Core.
    Import Paradoxes.
    
    (** From Omega's paradoxes, we can prove anything *)
    Theorem omega_proves_anything {Omega : OmegaType} :
      forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x.
    Proof.
      intros P x.
      destruct (omega_has_paradoxes P) as [w [Hw Hnw]].
      (* We have Hw : P w and Hnw : ~ P w, which is a contradiction *)
      contradiction.
    Qed.
    
    (** Principle of explosion holds universally *)
    Theorem explosion {Omega : OmegaType} :
      forall (A : Prop), A.
    Proof.
      intro A.
      exact (match omega_ex_falso with end).
    Qed.
    
    (** All elements are equal in Omega *)
    Theorem omega_all_equal {Omega : OmegaType} :
      forall (x y : Omegacarrier), x = y.
    Proof.
      intros x y.
      apply explosion.
    Qed.
    
  End Triviality.

  (** ** Characterization
      
      The fundamental equivalence between completeness and contradiction *)
  Module Characterization.
    
    Theorem omega_completeness_implies_contradiction {Omega : OmegaType} :
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y) ->
      exists R: Omegacarrier -> Prop, 
        (exists z: Omegacarrier, R z) /\ (forall z: Omegacarrier, R z -> False).
    Proof.
      intros omega_complete.
      set (R := fun _ : Omegacarrier => False).
      exists R.
      split.
      - apply omega_complete.
      - intros z Hz. exact Hz.
    Qed.

    Theorem contradiction_implies_omega_completeness {Omega : OmegaType} :
      (exists R: Omegacarrier -> Prop, 
        (exists z: Omegacarrier, R z) /\ (forall z: Omegacarrier, R z -> False)) ->
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y).
    Proof.
      intros [R [[z Hz] H_uninhab]] Q.
      exfalso.
      exact (H_uninhab z Hz).
    Qed.

    (** The fundamental characterization of Omega *)
    Theorem complete_iff_contradictory {Omega : OmegaType} :
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y) <->
      exists R: Omegacarrier -> Prop, 
        (exists z: Omegacarrier, R z) /\ (forall z: Omegacarrier, R z -> False).
    Proof.
      split.
      - apply omega_completeness_implies_contradiction.
      - apply contradiction_implies_omega_completeness.
    Qed.
    
  End Characterization.

  Export Core.
  Export Paradoxes.
  
End OmegaProperties.