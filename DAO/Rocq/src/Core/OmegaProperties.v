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

    Theorem inhabited_uninhabited_iff_all_inhabited {Omega : OmegaType} :
      (exists R: Omegacarrier -> Prop, 
        (exists z: Omegacarrier, R z) /\ (forall z: Omegacarrier, R z -> False)) <->
      ~ (exists R: Omegacarrier -> Prop, 
        forall z: Omegacarrier, R z -> False).
    Proof.
      split.
      
      (* Left to right: if R is both inhabited and uninhabited, 
        then no predicate can be uninhabited *)
      - intros [R [[witness HR_witness] HR_uninhabited]].
        intros [S HS_uninhabited].
        (* We have HR_witness : R witness, and HR_uninhabited says R witness -> False *)
        exact (HR_uninhabited witness HR_witness).
      
      (* Right to left: if every predicate is inhabited, 
        then False itself is inhabited, giving us our contradiction *)
      - intro H_no_uninhabited.
        (* The predicate "fun _ => False" should be uninhabited *)
        exfalso.
        apply H_no_uninhabited.
        exists (fun _ : Omegacarrier => False).
        intros z Hz.
        exact Hz.
    Qed.

    Theorem no_constraints_iff_constraints_exist {Omega : OmegaType} :
      ~ (exists R: Omegacarrier -> Prop, 
        forall z: Omegacarrier, R z -> False) <-> 
      (exists P: Omegacarrier -> Prop, 
        forall x: Omegacarrier, P x -> False).
    Proof.
      split.
      
      (* Forward: If no constraints exist, then a constraint exists *)
      - intro H_no_constraints.
        (* By omega_completeness, (fun _ => False) has a witness *)
        destruct (omega_completeness (fun _ : Omegacarrier => False)) as [x Hx].
        (* But this means we have a constraint! *)
        exfalso.
        apply H_no_constraints.
        exists (fun _ => False).
        intros z Hz.
        exact Hz.
      
      (* Backward: If a constraint exists, then no constraints exist *)
      - intros [P HP].
        (* We have P that's impossible (forall x, P x -> False) *)
        (* But by omega_completeness, P has a witness *)
        destruct (omega_completeness P) as [x Px].
        (* This is a contradiction *)
        exfalso.
        exact (HP x Px).
    Qed.
    
  End Characterization.

  Export Core.
  Export Paradoxes.
  
End OmegaProperties.

(** The Paradox of No Constraints (General Form):
    For ANY type T, having no constraints (everything is satisfiable) 
    is equivalent to being able to satisfy the unsatisfiable. *)
Theorem no_constraints_is_contradiction_general (T : Type) :
  (exists R: T -> Prop, 
    (exists z: T, R z) /\ (forall z: T, R z -> False)) <->
  ~ (exists R: T -> Prop, 
    forall z: T, R z -> False).
Proof.
  split.
  
  (* Forward: If we can satisfy the unsatisfiable,
     then there are no constraints *)
  - intros [R [[witness HR_witness] HR_impossible]].
    intros [S HS_constrains].
    exact (HR_impossible witness HR_witness).
  
  (* Backward: If there are no constraints,
     then even False must be satisfiable *)
  - intro H_no_constraints.
    exfalso.
    apply H_no_constraints.
    exists (fun _ : T => False).
    intros z Hz.
    exact Hz.
Qed.


(** Completeness is equivalent to having no constraints *)
Theorem completeness_iff_no_constraints (T : Type) :
  (forall P: T -> Prop, exists x: T, P x) <->
  ~ (exists R: T -> Prop, 
    forall z: T, R z -> False).
Proof.
  split.
  
  (* Forward: If every predicate is satisfiable (completeness),
     then no predicate can be unsatisfiable (no constraints) *)
  - intros H_complete [R HR_impossible].
    destruct (H_complete R) as [witness HR_witness].
    exact (HR_impossible witness HR_witness).
  
  (* Backward: If there are no constraints,
     then False itself is not a constraint - contradiction!
     From this contradiction, completeness follows. *)
  - intros H_no_constraints P.
    exfalso.
    apply H_no_constraints.
    exists (fun _ : T => False).
    intros z Hz.
    exact Hz.
Qed.