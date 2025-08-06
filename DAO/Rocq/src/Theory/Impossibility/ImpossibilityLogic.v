(** * ImpossibilityLogic.v
    
    Develops logical systems within AlphaType:
    - Bootstrap: Building logic from omega_veil and NAND
    - Three-valued logic with undecidable predicates
    - How Omega's completeness breaks Alpha's undecidability
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Core.OmegaType.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.

Module ImpossibilityLogic.
  Import ImpossibilityAlgebra.Core.
  
  (* ================================================================ *)
  (** ** Bootstrap: Building Logic from NAND *)
  Module Bootstrap.

    (* Define outside the section so they're directly accessible *)
    (** The first generated predicate: not omega_veil *)
    Definition alpha_0 {Alpha : AlphaType} : Alphacarrier -> Prop :=
    fun a => ~ omega_veil a.
  
    (** The primitive: NAND *)
    Definition NAND {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      fun a => ~ (P a /\ Q a).
    
    Section NANDConstruction.
      Context {Alpha : AlphaType}.
      
      (** alpha_0 is not impossible - it has witnesses *)
      Theorem alpha_0_not_impossible :
        ~ Is_Impossible alpha_0.
      Proof.
        intro H.
        assert (forall a, ~ omega_veil a <-> omega_veil a) by apply H.
        destruct alpha_not_empty as [a0 _].
        specialize (H0 a0).
        destruct H0 as [H1 H2].
        assert (~ omega_veil a0).
        { intro Hov. apply (H2 Hov). exact Hov. }
        apply H0. apply H1. exact H0.
      Qed.
      
      (** Generate logical operations from NAND *)
      Definition gen_not (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        NAND P P.
      
      Definition gen_and (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        gen_not (NAND P Q).
      
      Definition gen_or (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        NAND (NAND P P) (NAND Q Q).
      
      Definition gen_implies (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        gen_or (gen_not P) Q.
      
      Definition gen_true : Alphacarrier -> Prop :=
        NAND omega_veil alpha_0.
      
      Definition gen_false : Alphacarrier -> Prop :=
        omega_veil.
      
      (** Basic properties *)
      Theorem gen_not_omega_veil_is_alpha_0 :
        forall a, gen_not omega_veil a <-> alpha_0 a.
      Proof.
        intro a.
        unfold gen_not, alpha_0, NAND.
        split; intro H.
        - intro Hov. apply H. split; exact Hov.
        - intros [Hov _]. exact (H Hov).
      Qed.
      
      Theorem gen_true_exists :
        exists a, gen_true a.
      Proof.
        unfold gen_true, NAND, alpha_0.
        destruct alpha_not_empty as [a0 _].
        exists a0.
        intro H.
        destruct H as [Hov Hnov].
        exact (Hnov Hov).
      Qed.
      
      (** NAND properties *)
      Theorem nand_comm :
        forall P Q a, NAND P Q a <-> NAND Q P a.
      Proof.
        intros P Q a.
        unfold NAND.
        split; intro H; intro H_conj; apply H;
        destruct H_conj as [H1 H2]; split; assumption.
      Qed.
      
      (** Double negation elimination for omega_veil *)
      Lemma double_neg_omega_veil_impossible :
        Is_Impossible (fun a => ~ ~ omega_veil a).
      Proof.
        intro a.
        assert (H_no_witnesses: forall x, ~ (~ ~ omega_veil x)).
        { intros x H_nnov. apply H_nnov. exact (AlphaProperties.Core.omega_veil_has_no_witnesses x). }
        pose proof (AlphaProperties.Core.omega_veil_unique (fun x => ~ ~ omega_veil x) H_no_witnesses) as H_equiv.
        exact (H_equiv a).
      Qed.
      
      Theorem omega_veil_double_neg_elim : 
        forall a, ~ ~ omega_veil a -> omega_veil a.
      Proof.
        intros a H_nnov.
        apply double_neg_omega_veil_impossible.
        exact H_nnov.
      Qed.
      
      (** Truth table for the two-element algebra *)
      Theorem nand_omega_self :
        forall a, NAND omega_veil omega_veil a <-> alpha_0 a.
      Proof.
        intro a.
        unfold NAND, alpha_0.
        split; intro H.
        - intro Hov. apply H. split; exact Hov.
        - intros [Hov _]. exact (H Hov).
      Qed.
      
      Theorem nand_alpha_0_self :
        forall a, NAND alpha_0 alpha_0 a <-> omega_veil a.
      Proof.
        intro a.
        unfold NAND, alpha_0.
        split; intro H.
        - apply omega_veil_double_neg_elim.
          intro Hnov. apply H. split; exact Hnov.
        - intros [Hnov _]. exact (Hnov H).
      Qed.
      
      (** Complete behavior of implications *)
      Theorem gen_implies_omega_omega :
        forall a, gen_implies omega_veil omega_veil a.
      Proof.
        intro a.
        unfold gen_implies, gen_or, gen_not, NAND.
        intro H.
        destruct H as [H1 H2].
        apply H1. split; exact H2.
      Qed.
      
      Theorem gen_implies_omega_alpha :
        forall a, gen_implies omega_veil alpha_0 a <-> alpha_0 a.
      Proof.
        intro a.
        unfold gen_implies, gen_or, gen_not, alpha_0, NAND.
        split.
        - intro H. intro Hov. apply H. split.
          + intro H_conj. destruct H_conj as [H1 H2].
            apply H1. split; exact Hov.
          + intro H_conj. destruct H_conj as [H1 H2].
            exact (H1 Hov).
        - intro H_alpha. intro H_conj.
          destruct H_conj as [H1 H2].
          apply H2. split; exact H_alpha.
      Qed.
      
      Theorem gen_implies_alpha_omega :
        forall a, gen_implies alpha_0 omega_veil a <-> omega_veil a.
      Proof.
        intro a.
        unfold gen_implies, gen_or, gen_not, alpha_0, NAND.
        split.
        - intro H.
          apply omega_veil_double_neg_elim.
          intro H_not_omega.
          apply H. split.
          + intro H_conj. destruct H_conj as [H1 H2].
            apply H1. split; exact H_not_omega.
          + intro H_conj. destruct H_conj as [Hov _].
            exact (H_not_omega Hov).
        - intro Hov. intro H_conj.
          destruct H_conj as [H1 H2].
          apply H2. split; exact Hov.
      Qed.
      
      Theorem gen_implies_alpha_alpha :
        forall a, gen_implies alpha_0 alpha_0 a.
      Proof.
        intro a.
        unfold gen_implies, gen_or, gen_not, alpha_0, NAND.
        intro H.
        destruct H as [H1 H2].
        apply H1. split; exact H2.
      Qed.
      
      (** Summary: complete truth table *)
      Theorem gen_implies_complete :
        (forall a, gen_implies omega_veil omega_veil a) /\
        (forall a, gen_implies omega_veil alpha_0 a <-> alpha_0 a) /\
        (forall a, gen_implies alpha_0 omega_veil a <-> omega_veil a) /\
        (forall a, gen_implies alpha_0 alpha_0 a).
      Proof.
        split; [|split; [|split]].
        - exact gen_implies_omega_omega.
        - exact gen_implies_omega_alpha.
        - exact gen_implies_alpha_omega.
        - exact gen_implies_alpha_alpha.
      Qed.
      
    End NANDConstruction.
  End Bootstrap.
  
  (* ================================================================ *)
  (** ** Three-Valued Logic *)
  Module ThreeValued.
    Import Bootstrap.
    
    Section ThreeValuedDefinitions.
      Context {Alpha : AlphaType}.
      
      (** The three truth values *)
      Definition definitely_true (P : Alphacarrier -> Prop) : Prop :=
        exists a, P a.
      
      Definition definitely_false (P : Alphacarrier -> Prop) : Prop :=
        forall a, ~ P a.
      
      Definition undecidable (P : Alphacarrier -> Prop) : Prop :=
        ~ definitely_true P /\ ~ definitely_false P.
      
      (** Undecidable predicates and logical operations *)
      Theorem and_undecidable_not_true :
        forall P Q : Alphacarrier -> Prop,
        undecidable P ->
        undecidable Q ->
        ~ definitely_true (fun a => P a /\ Q a).
      Proof.
        intros P Q [HnP _] [HnQ _].
        unfold definitely_true in *.
        intro H.
        destruct H as [a [HPa HQa]].
        apply HnP. exists a. exact HPa.
      Qed.
      
      Theorem or_undecidable_not_false :
        forall P Q : Alphacarrier -> Prop,
        undecidable P ->
        ~ Is_Impossible (fun a => P a \/ Q a).
      Proof.
        intros P Q [H_not_true H_not_false].
        unfold Is_Impossible.
        intro H_impossible.
        assert (Is_Impossible P).
        { intro a. split.
          - intro HPa. apply H_impossible. left. exact HPa.
          - intro Hov. exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hov). }
        assert (definitely_false P).
        { unfold definitely_false. intros a HPa.
          apply H in HPa. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a HPa). }
        exact (H_not_false H0).
      Qed.
      
      (** The AND/OR duality for undecidable predicates *)
      Theorem undecidable_duality :
        forall P : Alphacarrier -> Prop,
        undecidable P ->
        (forall R, ~ definitely_true (fun a => P a /\ R a)) /\
        (forall R, ~ Is_Impossible (fun a => P a \/ R a)).
      Proof.
        intros P H_undec.
        destruct H_undec as [H_not_true H_not_false].
        split.
        - intros R. unfold definitely_true in *.
          intro H. destruct H as [a [HPa HRa]].
          apply H_not_true. exists a. exact HPa.
        - intros R. apply (or_undecidable_not_false P R).
          split; assumption.
      Qed.
      
      (** Interaction with extreme values *)
      Theorem undecidable_and_impossible :
        forall P Q : Alphacarrier -> Prop,
        undecidable P ->
        Is_Impossible Q ->
        Is_Impossible (fun a => P a /\ Q a).
      Proof.
        intros P Q H_undec H_Q_imp a.
        split.
        - intros [HPa HQa]. apply H_Q_imp. exact HQa.
        - intro Hov. exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hov).
      Qed.
      
      Theorem undecidable_and_true :
        forall P Q : Alphacarrier -> Prop,
        undecidable P ->
        (forall a, Q a) ->
        undecidable (fun a => P a /\ Q a).
      Proof.
        intros P Q [H_not_true H_not_false] H_Q_always.
        unfold undecidable, definitely_true, definitely_false.
        split.
        - intro H_exists.
          destruct H_exists as [a [HPa HQa]].
          apply H_not_true. exists a. exact HPa.
        - intro H_all_false.
          apply H_not_false.
          intros a HPa.
          apply (H_all_false a).
          split; [exact HPa | apply H_Q_always].
      Qed.
      
      (** The master theorem on extreme values *)
      Theorem extreme_values_master :
        forall P : Alphacarrier -> Prop,
        undecidable P ->
        (Is_Impossible (fun a => P a /\ omega_veil a)) /\
        (forall Q, (forall a, Q a) -> undecidable (fun a => P a /\ Q a)) /\
        (undecidable (fun a => P a \/ omega_veil a)) /\
        (forall Q, (forall a, Q a) -> forall a, (P a \/ Q a)).
      Proof.
        intros P H_P_undec.
        split; [|split; [|split]].
        - apply undecidable_and_impossible.
          + exact H_P_undec.
          + intro a. reflexivity.
        - intros Q H_Q_always.
          exact (undecidable_and_true P Q H_P_undec H_Q_always).
        - destruct H_P_undec as [H_not_true H_not_false].
          split.
          + unfold definitely_true in *.
            intro H_exists.
            destruct H_exists as [a [HPa | Hov]].
            * apply H_not_true. exists a. exact HPa.
            * exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hov).
          + unfold definitely_false in *.
            intro H_all_false.
            apply H_not_false.
            intros a HPa.
            apply (H_all_false a).
            left. exact HPa.
        - intros Q H_Q_always a.
          right. apply H_Q_always.
      Qed.
      
    End ThreeValuedDefinitions.
  End ThreeValued.
  
  (* ================================================================ *)
  (** ** Omega Oracles *)
  Module OmegaOracles.
    Import ThreeValued.
    
    Section OracleProperties.
      Context {Alpha : AlphaType} {Omega : OmegaType}.
      Variable embed : Alphacarrier -> Omegacarrier.
      
      (** Parameterized undecidability *)
      Definition undecidable_in {A : AlphaType} (P : @Alphacarrier A -> Prop) : Prop :=
        ~ (exists a : @Alphacarrier A, P a) /\ 
        ~ (forall a : @Alphacarrier A, ~ P a).
      
      (** Omega has witnesses for undecidable predicates *)
      Theorem undecidable_has_omega_witness :
        forall P : Alphacarrier -> Prop,
        undecidable_in P ->
        exists x : Omegacarrier, 
          (exists a : Alphacarrier, embed a = x /\ P a) \/
          (exists a : Alphacarrier, embed a = x /\ ~ P a).
      Proof.
        intros P H_undec.
        pose (omega_pred := fun x => 
          (exists a : Alphacarrier, embed a = x /\ P a) \/
          (exists a : Alphacarrier, embed a = x /\ ~ P a)).
        destruct (omega_completeness omega_pred) as [x Hx].
        exists x. exact Hx.
      Qed.
      
      (** Omega can decide the undecidable *)
      Theorem omega_decides_undecidable :
        forall P : Alphacarrier -> Prop,
        undecidable_in P ->
        exists oracle : Omegacarrier,
          ((exists a : Alphacarrier, P a) /\ 
           exists a : Alphacarrier, embed a = oracle /\ P a) \/
          ((forall a : Alphacarrier, ~ P a) /\ 
           exists a : Alphacarrier, embed a = oracle /\ ~ P a).
      Proof.
        intros P H_undec.
        pose (oracle_pred := fun x =>
          ((exists a : Alphacarrier, P a) /\ 
           exists a : Alphacarrier, embed a = x /\ P a) \/
          ((forall a : Alphacarrier, ~ P a) /\ 
           exists a : Alphacarrier, embed a = x /\ ~ P a)).
        destruct (omega_completeness oracle_pred) as [oracle H_oracle].
        exists oracle. exact H_oracle.
      Qed.
      
      (** Omega breaks undecidability with resolution *)
      Theorem omega_breaks_undecidability :
        forall P : Alphacarrier -> Prop,
        undecidable_in P ->
        exists x : Omegacarrier,
        exists resolution : bool,
          (resolution = true /\ exists a : Alphacarrier, embed a = x /\ P a) \/
          (resolution = false /\ exists a : Alphacarrier, embed a = x /\ ~ P a).
      Proof.
        intros P H_undec.
        destruct (omega_decides_undecidable P H_undec) as [oracle H_oracle].
        exists oracle.
        destruct H_oracle as [[H_exists H_witness] | [H_none H_witness]].
        - exists true. left. split; [reflexivity | exact H_witness].
        - exists false. right. split; [reflexivity | exact H_witness].
      Qed.
      
    End OracleProperties.
  End OmegaOracles.
  
  (* ================================================================ *)
  (** ** Generation Example *)
  Module Examples.
    Import Bootstrap.
    
    Section GenerationSequence.
      Context {Alpha : AlphaType}.
      
      (** Building complexity from impossibility *)
      Definition generation_sequence : nat -> (Alphacarrier -> Prop) :=
        fun n => match n with
        | 0 => omega_veil
        | 1 => alpha_0
        | 2 => gen_true
        | 3 => gen_and alpha_0 alpha_0
        | 4 => gen_or omega_veil alpha_0
        | _ => gen_true
        end.
      
      (** The sequence shows increasing structural complexity *)
      Theorem generation_increases_complexity :
        Is_Impossible (generation_sequence 0) /\
        ~ Is_Impossible (generation_sequence 1) /\
        exists a, (generation_sequence 2) a.
      Proof.
        split; [|split].
        - unfold generation_sequence. 
          intro a. split; intro H; exact H.
        - unfold generation_sequence.
          exact alpha_0_not_impossible.
        - unfold generation_sequence.
          exact gen_true_exists.
      Qed.
      
    End GenerationSequence.
  End Examples.
  
End ImpossibilityLogic.


(** * Classical Logic from Alpha
    
    This module shows how classical two-valued logic emerges as a special case
    within Alpha's three-valued system. Classical predicates are those that
    are "collapsed" to extreme values - either always omega_veil (false) or
    always alpha_0 (true).
*)

Module ClassicalLogic.
  Import ImpossibilityAlgebra.Core.
  Import ImpossibilityLogic.Bootstrap.
  
  (* ================================================================ *)
  (** ** Core Definitions *)
  Module Core.

    (** A predicate is classical if it equals one of the extreme values *)
    Definition is_classical {Alpha : AlphaType} (P : Alphacarrier -> Prop) : Prop :=
      (forall a, P a <-> omega_veil a) \/ (forall a, P a <-> alpha_0 a).
    
    Section ClassicalDefinitions.
      Context {Alpha : AlphaType}.
      
      (** The two base predicates are classical *)
      Theorem omega_veil_is_classical : is_classical omega_veil.
      Proof.
        unfold is_classical.
        left. intro a. reflexivity.
      Qed.
      
      Theorem alpha_0_is_classical : is_classical alpha_0.
      Proof.
        unfold is_classical.
        right. intro a. reflexivity.
      Qed.
      
    End ClassicalDefinitions.
  End Core.

  (* ================================================================ *)
  (** ** Truth Tables *)
  Module Tables.
    Import Core.
    Import ImpossibilityLogic.Bootstrap.
    
    Section TruthTables.
      Context {Alpha : AlphaType}.
      
      (** Helper lemmas for extensionality *)
      Lemma equals_omega_veil_iff :
        forall P a,
        (forall x, P x <-> omega_veil x) ->
        P a <-> omega_veil a.
      Proof.
        intros P a H_eq.
        exact (H_eq a).
      Qed.
      
      Lemma equals_alpha_0_iff :
        forall P a,
        (forall x, P x <-> alpha_0 x) ->
        P a <-> alpha_0 a.
      Proof.
        intros P a H_eq.
        exact (H_eq a).
      Qed.
      
      Lemma double_neg_conj_omega :
        forall P Q a,
        (forall x, P x <-> omega_veil x) ->
        (forall x, Q x <-> omega_veil x) ->
        ~ ~ (P a /\ Q a) <-> omega_veil a.
      Proof.
        intros P Q a H_P H_Q.
        split.
        - intro H_nn.
          apply omega_veil_double_neg_elim.
          intro H_not_omega.
          apply H_nn.
          intros [HPa HQa].
          apply H_P in HPa.
          exact (H_not_omega HPa).
        - intro H_omega.
          intro H_neg.
          apply H_neg.
          split; [apply H_P | apply H_Q]; exact H_omega.
      Qed.
      
      Lemma nand_self_is_not :
        forall P a,
        NAND P P a <-> ~ P a.
      Proof.
        intros P a.
        unfold NAND.
        split.
        - intros H HPa. apply H. split; exact HPa.
        - intros H [HPa _]. exact (H HPa).
      Qed.
      
      Lemma gen_and_to_double_neg :
        forall P Q a,
        gen_and P Q a <-> ~ ~ (P a /\ Q a).
      Proof.
        intros P Q a.
        unfold gen_and, gen_not, NAND.
        split.
        - intro H.
          intro H_neg.
          apply H.
          split; exact H_neg.
        - intro H_nn.
          intros [H1 H2].
          exact (H_nn H1).
      Qed.
      
      Lemma gen_and_extensional :
        forall P P' Q Q' a,
        (forall x, P x <-> P' x) ->
        (forall x, Q x <-> Q' x) ->
        gen_and P Q a <-> gen_and P' Q' a.
      Proof.
        intros P P' Q Q' a H_P H_Q.
        unfold gen_and, gen_not, NAND.
        split.
        - intro H.
          intro H_nand'.
          apply H.
          destruct H_nand' as [H1' H2'].
          split.
          + intro H_PQ.
            apply H1'.
            destruct H_PQ as [HPa HQa].
            split.
            * apply H_P. exact HPa.
            * apply H_Q. exact HQa.
          + intro H_PQ.
            apply H2'.
            destruct H_PQ as [HPa HQa].
            split.
            * apply H_P. exact HPa.
            * apply H_Q. exact HQa.
        - intro H.
          intro H_nand.
          apply H.
          destruct H_nand as [H1 H2].
          split.
          + intro H_P'Q'.
            apply H1.
            destruct H_P'Q' as [HP'a HQ'a].
            split.
            * apply H_P. exact HP'a.
            * apply H_Q. exact HQ'a.
          + intro H_P'Q'.
            apply H2.
            destruct H_P'Q' as [HP'a HQ'a].
            split.
            * apply H_P. exact HP'a.
            * apply H_Q. exact HQ'a.
      Qed.
      
      Lemma nand_extensional :
        forall P P' Q Q' a,
        (forall x, P x <-> P' x) ->
        (forall x, Q x <-> Q' x) ->
        NAND P Q a <-> NAND P' Q' a.
      Proof.
        intros P P' Q Q' a H_P H_Q.
        unfold NAND.
        split; intro H; intro H_conj; apply H; 
        destruct H_conj as [H1 H2]; split;
        [apply H_P | apply H_Q | apply H_P | apply H_Q]; assumption.
      Qed.
      
      Lemma gen_or_extensional :
        forall P P' Q Q' a,
        (forall x, P x <-> P' x) ->
        (forall x, Q x <-> Q' x) ->
        gen_or P Q a <-> gen_or P' Q' a.
      Proof.
        intros P P' Q Q' a H_P H_Q.
        unfold gen_or.
        apply nand_extensional.
        - intro x. apply nand_extensional; auto.
        - intro x. apply nand_extensional; auto.
      Qed.
      
      (** Commutativity lemmas *)
      Theorem classical_or_comm :
        forall P Q, is_classical P -> is_classical Q ->
        forall a, gen_or P Q a <-> gen_or Q P a.
      Proof.
        intros P Q H_P H_Q a.
        unfold gen_or, NAND.
        split; intro H; intro H_conj; apply H;
        destruct H_conj as [H1 H2]; split; assumption.
      Qed.
      
      Theorem classical_and_comm :
        forall P Q, is_classical P -> is_classical Q ->
        forall a, gen_and P Q a <-> gen_and Q P a.
      Proof.
        intros P Q H_P H_Q a.
        unfold gen_and, gen_not, NAND.
        split; intro H; intro H_nand; apply H; destruct H_nand as [H1 H2]; split;
        intro H_conj; [apply H1 | apply H2 | apply H1 | apply H2];
        destruct H_conj as [HPa HQa]; split; assumption.
      Qed.
      
      (** Truth tables for NOT *)
      Lemma classical_not_table :
        (forall a, gen_not omega_veil a <-> alpha_0 a) /\
        (forall a, gen_not alpha_0 a <-> omega_veil a).
      Proof.
        split.
        - intro a. unfold gen_not, NAND, alpha_0.
          split; intro H.
          + intro Hov. apply H. split; exact Hov.
          + intros [Hov _]. exact (H Hov).
        - intro a. unfold gen_not, NAND, alpha_0.
          split; intro H.
          + apply omega_veil_double_neg_elim.
            intro Hnov. apply H. split; exact Hnov.
          + intros [Hnov _]. exact (Hnov H).
      Qed.

      Theorem gen_and_omega_alpha :
        forall a, gen_and omega_veil alpha_0 a <-> omega_veil a.
      Proof.
        intro a.
        unfold gen_and, gen_not, NAND.
        split; intro H.
        - apply omega_veil_double_neg_elim.
          intro H_not_ov.
          apply H.
          split; intro H_conj; destruct H_conj as [Hov _]; exact (H_not_ov Hov).
        - intro H_not.
          apply H_not.
          split.
          + exact H.
          + exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
      Qed.

      Theorem gen_or_omega_alpha :
        forall a, gen_or omega_veil alpha_0 a <-> alpha_0 a.
      Proof.
        intro a.
        unfold gen_or, NAND.
        split; intro H.
        - (* Forward direction *)
          intro Hov.
          apply H.
          split.
          + (* ~ (omega_veil a /\ omega_veil a) *)
            intro H_conj.
            destruct H_conj as [Hov1 _].
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hov1).
          + (* ~ (alpha_0 a /\ alpha_0 a) *)
            intro H_conj.
            destruct H_conj as [Ha0 _].
            unfold alpha_0 in Ha0.
            exact (Ha0 Hov).
        - (* Backward direction *)
          intro H_conj.
          destruct H_conj as [H_omega_nand H_alpha_nand].
          unfold alpha_0 in H.
          apply H_alpha_nand.
          split; exact H.
      Qed.
      
      (** Truth tables for AND *)
      Lemma classical_and_table :
        (forall a, gen_and omega_veil omega_veil a <-> omega_veil a) /\
        (forall a, gen_and omega_veil alpha_0 a <-> omega_veil a) /\
        (forall a, gen_and alpha_0 omega_veil a <-> omega_veil a) /\
        (forall a, gen_and alpha_0 alpha_0 a <-> alpha_0 a).
      Proof.
        split; [|split; [|split]].
        - intro a.
          rewrite gen_and_to_double_neg.
          split.
          + intro H. exfalso. apply H. intros [H1 H2]. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H1).
          + intro H. intro H_neg. exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
        - apply gen_and_omega_alpha.
        - intro a.
          rewrite gen_and_to_double_neg.
          split.
          + intro H_nn.
            exfalso.
            apply H_nn.
            intros [H_alpha H_omega].
            unfold alpha_0 in H_alpha.
            exact (H_alpha H_omega).
          + intro H_omega.
            exfalso.
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H_omega).
        - intro a.
          rewrite gen_and_to_double_neg.
          split.
          + intro H_nn. unfold alpha_0. intro H_omega.
            apply H_nn. intros [_ _]. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H_omega).
          + intro H_alpha. intro H_neg. apply H_neg. split; exact H_alpha.
      Qed.
      
      (** Truth tables for OR *)
      Lemma classical_or_table :
        (forall a, gen_or omega_veil omega_veil a <-> omega_veil a) /\
        (forall a, gen_or omega_veil alpha_0 a <-> alpha_0 a) /\
        (forall a, gen_or alpha_0 omega_veil a <-> alpha_0 a) /\
        (forall a, gen_or alpha_0 alpha_0 a <-> alpha_0 a).
      Proof.
        split; [|split; [|split]].
        - intro a. unfold gen_or, NAND.
          split.
          + intro H. apply omega_veil_double_neg_elim. intro H_not.
            apply H. split; intros [H1 H2]; exact (H_not H1).
          + intro H_omega. intro H_conj. destruct H_conj as [H1 H2].
            apply H1. split; exact H_omega.
        - apply gen_or_omega_alpha.
        - intro a.
          rewrite classical_or_comm; auto using omega_veil_is_classical, alpha_0_is_classical.
          apply gen_or_omega_alpha.
        - intro a. unfold gen_or, NAND, alpha_0.
          split.
          + intro H. intro H_omega. apply H.
            split; intros [H1 H2]; exact (H1 H_omega).
          + intro H_not_omega. intro H_conj.
            destruct H_conj as [H1 H2]. apply H1. split; exact H_not_omega.
      Qed.
      
    End TruthTables.
  End Tables.
  
  (* ================================================================ *)
  (** ** Closure Properties *)
  Module Closure.
    Import Core.
    Import Tables.
    
    Section ClosureTheorems.
      Context {Alpha : AlphaType}.
      
      (** NOT preserves classical *)
      Theorem classical_closed_under_not :
        forall P, is_classical P -> is_classical (gen_not P).
      Proof.
        intros P H_classical.
        unfold is_classical in *.
        destruct H_classical as [H_omega | H_alpha].
        - (* P = omega_veil, so gen_not P = alpha_0 *)
          right.
          intro a.
          unfold gen_not, NAND.
          split.
          + intro H_nand.
            unfold alpha_0.
            intro H_ov.
            apply H_nand.
            split; apply H_omega; exact H_ov.
          + intro H_alpha0.
            intros [HPa1 HPa2].
            apply H_omega in HPa1.
            unfold alpha_0 in H_alpha0.
            exact (H_alpha0 HPa1).
        - (* P = alpha_0, so gen_not P = omega_veil *)
          left.
          intro a.
          unfold gen_not, NAND.
          split.
          + intro H_nand.
            apply omega_veil_double_neg_elim.
            intro H_not_omega.
            apply H_nand.
            split; apply H_alpha; unfold alpha_0; exact H_not_omega.
          + intro H_omega.
            intros [HPa1 HPa2].
            apply H_alpha in HPa1.
            unfold alpha_0 in HPa1.
            exact (HPa1 H_omega).
      Qed.
      
      (** AND preserves classical *)
      Theorem classical_closed_under_and :
        forall P Q, is_classical P -> is_classical Q -> is_classical (gen_and P Q).
      Proof.
        intros P Q H_P H_Q.
        unfold is_classical in *.
        destruct H_P as [H_P_omega | H_P_alpha];
        destruct H_Q as [H_Q_omega | H_Q_alpha].
        - (* P = omega_veil, Q = omega_veil *)
          left.
          intro a.
          rewrite gen_and_to_double_neg.
          rewrite double_neg_conj_omega; auto.
          reflexivity.
        - (* P = omega_veil, Q = alpha_0 *)
          left.
          intro a.
          rewrite (gen_and_extensional P omega_veil Q alpha_0); auto.
          apply gen_and_omega_alpha.
        - (* P = alpha_0, Q = omega_veil *)
          left.
          intro a.
          rewrite gen_and_to_double_neg.
          split.
          + intro H_nn.
            exfalso.
            apply H_nn.
            intros [HPa HQa].
            apply H_P_alpha in HPa.
            apply H_Q_omega in HQa.
            unfold alpha_0 in HPa.
            exact (HPa HQa).
          + intro H_omega.
            exfalso.
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H_omega).
        - (* P = alpha_0, Q = alpha_0 *)
          right.
          intro a.
          rewrite gen_and_to_double_neg.
          split.
          + intro H_nn.
            unfold alpha_0.
            intro H_omega.
            apply H_nn.
            intros [HPa HQa].
            apply H_P_alpha in HPa.
            unfold alpha_0 in HPa.
            exact (HPa H_omega).
          + intro H_alpha.
            intro H_neg.
            apply H_neg.
            split.
            * apply H_P_alpha. exact H_alpha.
            * apply H_Q_alpha. exact H_alpha.
      Qed.
      
      (** OR preserves classical *)
      Theorem classical_closed_under_or :
        forall P Q, is_classical P -> is_classical Q -> is_classical (gen_or P Q).
      Proof.
        intros P Q H_P H_Q.
        unfold is_classical in *.
        destruct H_P as [H_P_omega | H_P_alpha];
        destruct H_Q as [H_Q_omega | H_Q_alpha].
        - (* P = omega_veil, Q = omega_veil *)
          left.
          intro a.
          unfold gen_or, NAND.
          split.
          + intro H.
            apply omega_veil_double_neg_elim.
            intro H_not_omega.
            apply H.
            split.
            * intros [HP1 HP2].
              apply H_P_omega in HP1.
              exact (H_not_omega HP1).
            * intros [HQ1 HQ2].
              apply H_Q_omega in HQ1.
              exact (H_not_omega HQ1).
          + intro H_omega.
            intro H_conj.
            destruct H_conj as [H_nand_P H_nand_Q].
            apply H_nand_P.
            split; apply H_P_omega; exact H_omega.
        - (* P = omega_veil, Q = alpha_0 *)
          right.
          intro a.
          rewrite (gen_or_extensional P omega_veil Q alpha_0); auto.
          apply gen_or_omega_alpha.
        - (* P = alpha_0, Q = omega_veil *)
          right.
          intro a.
          rewrite (gen_or_extensional P alpha_0 Q omega_veil); auto.
          rewrite classical_or_comm; auto using alpha_0_is_classical, omega_veil_is_classical.
          apply gen_or_omega_alpha.
        - (* P = alpha_0, Q = alpha_0 *)
          right.
          intro a.
          unfold gen_or.
          rewrite (nand_extensional (NAND P P) omega_veil (NAND Q Q) omega_veil).
          + apply nand_omega_self.
          + intro x.
            rewrite (nand_extensional P alpha_0 P alpha_0); auto.
            apply nand_alpha_0_self.
          + intro x.
            rewrite (nand_extensional Q alpha_0 Q alpha_0); auto.
            apply nand_alpha_0_self.
      Qed.
      
      (** IMPLIES preserves classical *)
      Theorem classical_closed_under_implies :
        forall P Q, is_classical P -> is_classical Q -> is_classical (gen_implies P Q).
      Proof.
        intros P Q H_P H_Q.
        unfold gen_implies.
        apply classical_closed_under_or.
        - apply classical_closed_under_not. exact H_P.
        - exact H_Q.
      Qed.
      
    End ClosureTheorems.
  End Closure.
  
  
  (* ================================================================ *)
  (** ** Classical Laws *)
  Module Laws.
    Import Core Closure Tables.
    
    Section ClassicalLaws.
      Context {Alpha : AlphaType}.
      
      (** Excluded middle holds for classical predicates *)
      Theorem classical_excluded_middle :
        forall P, is_classical P -> (exists a, P a) \/ (forall a, ~ P a).
      Proof.
        intros P H_classical.
        unfold is_classical in H_classical.
        destruct H_classical as [H_omega | H_alpha].
        - (* P = omega_veil *)
          right.
          intros a H_Pa.
          apply H_omega in H_Pa.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H_Pa).
        - (* P = alpha_0 *)
          left.
          destruct alpha_not_empty as [a0 _].
          exists a0.
          apply H_alpha.
          unfold alpha_0.
          intro H_omega.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses a0 H_omega).
      Qed.
      
      (** Double negation elimination for classical predicates *)
      Theorem classical_double_neg_elim :
        forall P, is_classical P -> forall a, gen_not (gen_not P) a -> P a.
      Proof.
        intros P H_classical a H_nn.
        destruct H_classical as [H_omega | H_alpha].
        - (* P = omega_veil *)
          apply H_omega.
          unfold gen_not, NAND in H_nn.
          apply omega_veil_double_neg_elim.
          intro H_not_omega.
          apply H_nn.
          split.
          + intros [HPa1 HPa2].
            apply H_omega in HPa1.
            exact (H_not_omega HPa1).
          + intros [HPa1 HPa2].
            apply H_omega in HPa1.
            exact (H_not_omega HPa1).
        - (* P = alpha_0 *)
          apply H_alpha.
          unfold alpha_0.
          intro H_omega_a.
          unfold gen_not, NAND in H_nn.
          apply H_nn.
          split.
          + intros [HPa1 HPa2].
            apply H_alpha in HPa1.
            unfold alpha_0 in HPa1.
            exact (HPa1 H_omega_a).
          + intros [HPa1 HPa2].
            apply H_alpha in HPa1.
            unfold alpha_0 in HPa1.
            exact (HPa1 H_omega_a).
      Qed.
      
      (** De Morgan's law *)
      Theorem classical_demorgan_and :
        forall P Q, 
        is_classical P -> is_classical Q ->
        forall a, gen_not (gen_and P Q) a <-> gen_or (gen_not P) (gen_not Q) a.
      Proof.
        intros P Q H_P H_Q a.
        destruct classical_and_table as [H_om_om [H_om_al [H_al_om H_al_al]]].
        destruct classical_or_table as [H_or_om_om [H_or_om_al [H_or_al_om H_or_al_al]]].
        destruct classical_not_table as [H_not_om H_not_al].
        
        destruct H_P as [HP_om | HP_al]; destruct H_Q as [HQ_om | HQ_al].
        - (* P = omega, Q = omega *)
          assert (H_LHS: gen_not (gen_and P Q) a <-> alpha_0 a).
          { unfold gen_not, NAND.
            assert (gen_and P Q a <-> omega_veil a).
            { rewrite (gen_and_extensional P omega_veil Q omega_veil); auto. }
            rewrite H.
            split.
            - intro H_not. unfold alpha_0. intro H_omega. 
              apply H_not. split; exact H_omega.
            - intro H_alpha. intros [H1 H2].
              unfold alpha_0 in H_alpha. exact (H_alpha H1). }
          
          assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> alpha_0 a).
          { assert (H_notP_eq: forall x, gen_not P x <-> alpha_0 x).
            { intro x. unfold gen_not, NAND. rewrite !HP_om. apply nand_omega_self. }
            assert (H_notQ_eq: forall x, gen_not Q x <-> alpha_0 x).
            { intro x. unfold gen_not, NAND. rewrite !HQ_om. apply nand_omega_self. }
            rewrite (gen_or_extensional (gen_not P) alpha_0 (gen_not Q) alpha_0); auto. }
          
          rewrite H_LHS, H_RHS.
          reflexivity.
          
        - (* P = omega, Q = alpha *)
          assert (H_LHS: gen_not (gen_and P Q) a <-> alpha_0 a).
          { unfold gen_not, NAND.
            assert (gen_and P Q a <-> omega_veil a).
            { rewrite (gen_and_extensional P omega_veil Q alpha_0); auto. }
            rewrite H.
            split.
            - intro H_not. unfold alpha_0. intro H_omega. 
              apply H_not. split; exact H_omega.
            - intro H_alpha. intros [H1 H2].
              unfold alpha_0 in H_alpha. exact (H_alpha H1). }
          
          assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> alpha_0 a).
          { assert (H_notP_eq: forall x, gen_not P x <-> alpha_0 x).
            { intro x. unfold gen_not, NAND. rewrite !HP_om. apply nand_omega_self. }
            assert (H_notQ_eq: forall x, gen_not Q x <-> omega_veil x).
            { intro x. unfold gen_not, NAND. rewrite !HQ_al. apply nand_alpha_0_self. }
            rewrite (gen_or_extensional (gen_not P) alpha_0 (gen_not Q) omega_veil); auto. }
          
          rewrite H_LHS, H_RHS.
          reflexivity.
          
        - (* P = alpha, Q = omega *)
          assert (H_LHS: gen_not (gen_and P Q) a <-> alpha_0 a).
          { unfold gen_not, NAND.
            assert (gen_and P Q a <-> omega_veil a).
            { rewrite (gen_and_extensional P alpha_0 Q omega_veil); auto. }
            rewrite H.
            split.
            - intro H_not. unfold alpha_0. intro H_omega. 
              apply H_not. split; exact H_omega.
            - intro H_alpha. intros [H1 H2].
              unfold alpha_0 in H_alpha. exact (H_alpha H1). }
          
          assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> alpha_0 a).
          { assert (H_notP_eq: forall x, gen_not P x <-> omega_veil x).
            { intro x. unfold gen_not, NAND. rewrite !HP_al. apply nand_alpha_0_self. }
            assert (H_notQ_eq: forall x, gen_not Q x <-> alpha_0 x).
            { intro x. unfold gen_not, NAND. rewrite !HQ_om. apply nand_omega_self. }
            rewrite (gen_or_extensional (gen_not P) omega_veil (gen_not Q) alpha_0); auto. }
          
          rewrite H_LHS, H_RHS.
          reflexivity.
          
        - (* P = alpha, Q = alpha *)
          assert (H_LHS: gen_not (gen_and P Q) a <-> omega_veil a).
          { unfold gen_not, NAND.
            assert (gen_and P Q a <-> alpha_0 a).
            { rewrite (gen_and_extensional P alpha_0 Q alpha_0); auto. }
            rewrite H.
            split.
            - intro H_not. 
              apply omega_veil_double_neg_elim. intro H_not_omega.
              apply H_not. split; unfold alpha_0; exact H_not_omega.
            - intro H_omega. intros [H1 H2].
              unfold alpha_0 in H1. exact (H1 H_omega). }
          
          assert (H_RHS: gen_or (gen_not P) (gen_not Q) a <-> omega_veil a).
          { assert (H_notP_eq: forall x, gen_not P x <-> omega_veil x).
            { intro x. unfold gen_not, NAND. rewrite !HP_al. apply nand_alpha_0_self. }
            assert (H_notQ_eq: forall x, gen_not Q x <-> omega_veil x).
            { intro x. unfold gen_not, NAND. rewrite !HQ_al. apply nand_alpha_0_self. }
            rewrite (gen_or_extensional (gen_not P) omega_veil (gen_not Q) omega_veil); auto. }
          
          rewrite H_LHS, H_RHS.
          reflexivity.
      Qed.
      
      (** Contradiction principle *)
      Theorem classical_contradiction :
        forall P, is_classical P ->
        forall a, ~ (P a /\ gen_not P a).
      Proof.
        intros P H_P a [HPa HnotPa].
        destruct H_P as [HP_om | HP_al].
        - (* P = omega_veil *)
          apply HP_om in HPa.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses a HPa).
        - (* P = alpha_0 *)
          unfold gen_not, NAND in HnotPa.
          apply HnotPa.
          split; exact HPa.
      Qed.
      
      (** Proof by cases *)
      Theorem classical_cases :
        forall P Q R, is_classical P -> is_classical Q -> is_classical R ->
        (forall a, P a -> R a) ->
        (forall a, Q a -> R a) ->
        forall a, gen_or P Q a -> R a.
      Proof.
        intros P Q R H_P H_Q H_R H_PR H_QR a H_or.
        destruct H_P as [HP_om | HP_al]; destruct H_Q as [HQ_om | HQ_al].
        - (* P = omega, Q = omega *)
          assert (gen_or P Q a <-> omega_veil a).
          { rewrite (gen_or_extensional P omega_veil Q omega_veil); auto.
            apply (proj1 classical_or_table). }
          assert (omega_veil a) by (apply H; exact H_or).
          exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H0).
          
        - (* P = omega, Q = alpha *)
          apply H_QR.
          apply HQ_al.
          assert (gen_or P Q a <-> alpha_0 a).
          { rewrite (gen_or_extensional P omega_veil Q alpha_0); auto.
            apply (proj1 (proj2 classical_or_table)). }
          apply H. exact H_or.
          
        - (* P = alpha, Q = omega *)
          apply H_PR.
          apply HP_al.
          assert (gen_or P Q a <-> alpha_0 a).
          { rewrite (gen_or_extensional P alpha_0 Q omega_veil); auto.
            apply (proj1 (proj2 (proj2 classical_or_table))). }
          apply H. exact H_or.
          
        - (* P = alpha, Q = alpha *)
          apply H_PR.
          apply HP_al.
          assert (gen_or P Q a <-> alpha_0 a).
          { rewrite (gen_or_extensional P alpha_0 Q alpha_0); auto.
            apply (proj2 (proj2 (proj2 classical_or_table))). }
          apply H. exact H_or.
      Qed.
      
      (** Modus ponens *)
      Theorem classical_modus_ponens :
        forall P Q, is_classical P -> is_classical Q ->
        forall a, P a -> gen_implies P Q a -> Q a.
      Proof.
        intros P Q H_P H_Q a HPa Himp.
        unfold gen_implies in Himp.
        
        destruct H_P as [HP_om | HP_al]; destruct H_Q as [HQ_om | HQ_al].
        - (* P = omega, Q = omega *)
          apply HP_om in HPa.
          exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a HPa).
          
        - (* P = omega, Q = alpha *)
          apply HP_om in HPa.
          exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a HPa).
          
        - (* P = alpha, Q = omega *)
          apply HQ_om.
          assert (gen_implies P Q a <-> omega_veil a).
          { unfold gen_implies.
            rewrite (gen_or_extensional (gen_not P) omega_veil Q omega_veil); auto.
            - apply (proj1 classical_or_table).
            - intro x. unfold gen_not, NAND. rewrite !HP_al. apply nand_alpha_0_self. }
          apply H. exact Himp.
          
        - (* P = alpha, Q = alpha *)
          apply HQ_al. unfold alpha_0.
          intro H_omega.
          apply HP_al in HPa. unfold alpha_0 in HPa.
          exact (HPa H_omega).
      Qed.
      
    End ClassicalLaws.
  End Laws.
  
End ClassicalLogic.