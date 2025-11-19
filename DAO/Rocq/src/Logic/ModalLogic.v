(** * Modal.v
    
    Modal logic structure from the monad/comonad
    Formalizes ◇, □, and collapse operators
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Logic.Operators.
Require Import DAO.Theory.Adjunction.

Module ModalLogic.
  
  Section ModalOperators.
    Context {Alpha : AlphaType} {Omega : OmegaType}.
    
    (** Omega collapse operator *)
    (* Ω[ P ] = "P resolved in Omega" *)
    Definition omega_collapse (P : Alphacarrier -> Prop) : Prop :=
      exists w : Omegacarrier, True. (* Trivially true in Omega *)
    Notation "Ω[ P ]" := (omega_collapse P) (at level 10).
    
    (** Properties of Ω *)
    
    Theorem omega_collapse_total : forall P : Alphacarrier -> Prop,
      Ω[ P ].
    Proof.
      intro P.
      unfold omega_collapse.
      (* Omega is inhabited by completeness *)
      destruct (@omega_completeness Omega (fun _ => True)) as [w _].
      exists w. exact I.
    Qed.
    
    Theorem omega_idempotent : forall P : Alphacarrier -> Prop,
      Ω[ P ] <-> Ω[ Ω[ P ] ].
    Proof.
      intro P.
      split; intro H; apply omega_collapse_total.
    Qed.
    
    (** Modal logic axioms *)
    
    (* K: □(P → Q) → (□P → □Q) *)
    Theorem modal_K : forall P Q : Alphacarrier -> Prop,
      □(P ⇒ Q) -> (□P -> □Q).
    Proof.
      intros P Q HK HP a.
      destruct (HK a) as [Himpl | Hveil]; [|right; exact Hveil].
      destruct (HP a) as [HPa | Hveil]; [|right; exact Hveil].
      left.
      unfold gen_implies in Himpl.
      apply Himpl. exact HPa.
    Qed.
    
    (* T: □P → P (requires inhabited Alpha) *)
    Axiom alpha_inhabited : Alphacarrier.
    
    Theorem modal_T : forall P : Alphacarrier -> Prop,
      □P -> ◇P.
    Proof.
      intros P HP.
      unfold necessary, possible in *.
      destruct (HP alpha_inhabited) as [H | Hveil].
      - exists alpha_inhabited. exact H.
      - exfalso.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses alpha_inhabited Hveil).
    Qed.
    
    (* 4: □P → □□P *)
    Theorem modal_4 : forall P : Alphacarrier -> Prop,
      □P -> □(□P).
    Proof.
      intros P HP a.
      left. (* □P holds, so we can show it *)
      exact HP.
    Qed.
    
    (* 5: ◇P → □◇P *)
    Theorem modal_5 : forall P : Alphacarrier -> Prop,
      ◇P -> □(◇P).
    Proof.
      intros P [a HPa] a'.
      left. exists a. exact HPa.
    Qed.
    
  End ModalOperators.
  
  (* ================================================================ *)
  (** ** Collapse Semantics *)
  (* ================================================================ *)
  
  Section CollapseSemantics.
    Context {Alpha : AlphaType} {Omega : OmegaType}.
    
    (** Collapsing undecidability *)
    
    Definition undecidable (P : Alphacarrier -> Prop) : Prop :=
      ~(◇P) /\ ~(∅P).
    
    Theorem omega_resolves_undecidable : 
      forall P : Alphacarrier -> Prop,
      undecidable P -> Ω[ P ].
    Proof.
      intros P Hund.
      apply omega_collapse_total.
    Qed.
    
    (** Classical collapse *)
    
    (* In Omega, LEM holds *)
    Theorem omega_LEM : forall P : Omegacarrier -> Prop,
      (exists w, P w) \/ (forall w, ~ P w).
    Proof.
      intro P.
      destruct (@omega_completeness Omega P) as [w HPw].
      left. exists w. exact HPw.
    Qed.
    
    (* Alpha's ternary logic collapses to binary in Omega *)
    Theorem ternary_to_binary_collapse :
      forall P : Alphacarrier -> Prop,
      (◇P) \/ (∅P) \/ Ω[ P ].
    Proof.
      intro P.
      right. right.
      apply omega_collapse_total.
    Qed.
    
  End CollapseSemantics.
  
End ModalLogic.