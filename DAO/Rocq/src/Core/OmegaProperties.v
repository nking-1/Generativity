Require Import DAO.Core.OmegaType.

(** ** Properties of OmegaType *)

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

  (** Completeness is equivalent to having contradictory predicates *)
  Theorem omega_completeness_requires_contradiction :
    forall `{H_O: OmegaType},
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y) <->
      (exists R: Omegacarrier -> Prop, forall z: Omegacarrier, R z -> False).
  Proof.
    intros H_O.
    split.

    (* -> direction: completeness implies existence of an uninhabitable predicate *)
    intros omega_complete.

    set (P := fun x : Omegacarrier => ~ exists y : Omegacarrier, x = y).

    (* By omega_completeness, this predicate must have a witness *)
    destruct (omega_completeness P) as [x Hx].

    (* So we return P as the uninhabitable predicate (even though it's now inhabited) *)
    exists P.

    (* Now show: forall z, P z -> False *)
    intros z Hz.
    (* P z = ~ exists y, z = y, but clearly z = z, so contradiction *)
    apply Hz.
    exists z. reflexivity.

    (* <- direction: If there exists an uninhabitable predicate, Omega is complete *)
    intros [R H_uninhabitable].

    (* Let Q be any predicate *)
    intros Q.
    (* By omega_completeness, Q must have a witness *)
    apply omega_completeness.
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