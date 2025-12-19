(** ImpossibilityCalculus.v
    
    Develops a calculus for reasoning about predicate transformations
    and their convergence properties. We introduce notions of continuity,
    convergence, and paths in the space of predicates over AlphaType.
    
    Key concepts:
    - Convergence of predicate sequences
    - Continuity of predicate transformations
    - Observable differences between predicates
    - Paths through predicate space
    - Limits and fixed points
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Classes.RelationClasses.
From Stdlib Require Import Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

Module ImpossibilityCalculus.
  Import ImpossibilityAlgebra.Core.
  
  (* ================================================================ *)
  (** ** Core Definitions
      
      Basic definitions for working with sequences and agreement between
      predicates. These form the foundation for our convergence theory. *)
  Module Core.
    Section CoreDefinitions.
      Context {Alpha : AlphaType}.
      
      (** A sequence of predicates indexed by natural numbers *)
      Definition predicate_sequence := nat -> (Alphacarrier -> Prop).
      
      (** Two predicates agree at a specific point *)
      Definition agrees_at (P Q : Alphacarrier -> Prop) (a : Alphacarrier) : Prop :=
        P a <-> Q a.
      
      (** Agreement extends to a list of test points *)
      Definition agrees_on_list (P Q : Alphacarrier -> Prop) (witnesses : list Alphacarrier) : Prop :=
        forall a, In a witnesses -> agrees_at P Q a.
      
      (** Agreement is an equivalence relation *)
      Theorem agrees_at_equivalence :
        forall a, Equivalence (fun P Q => agrees_at P Q a).
      Proof.
        intro a.
        split.
        - (* Reflexivity *) 
          intro P. unfold agrees_at. reflexivity.
        - (* Symmetry *)
          intros P Q H. unfold agrees_at in *. 
          split; intro; apply H; assumption.
        - (* Transitivity *)
          intros P Q R HPQ HQR. unfold agrees_at in *.
          split; intro H.
          + apply HQR. apply HPQ. exact H.
          + apply HPQ. apply HQR. exact H.
      Qed.
      
    End CoreDefinitions.
  End Core.
  
  (* ================================================================ *)
  (** ** Convergence Theory
      
      This module develops the theory of convergence for predicate sequences.
      We define what it means for a sequence of predicates to converge to a
      limit predicate, and explore various convergence phenomena. *)
  Module Convergence.
    Import Core.
    
    (** *** Basic Definitions *)
    Section Definitions.
      Context {Alpha : AlphaType}.
      
      (** A sequence converges to P if it eventually agrees with P on any finite set *)
      Definition converges_to (seq : predicate_sequence) (P : Alphacarrier -> Prop) : Prop :=
        forall (witnesses : list Alphacarrier),
        exists N : nat,
        forall n : nat,
        n >= N ->
        agrees_on_list (seq n) P witnesses.
      
      (** Special case: approaching the impossible predicate *)
      Definition approaches_impossible (seq : predicate_sequence) : Prop :=
        converges_to seq omega_veil.
      
      (** Uniform convergence on a specific set *)
      Definition converges_uniformly_on (seq : predicate_sequence) (P : Alphacarrier -> Prop) 
                                       (S : list Alphacarrier) : Prop :=
        exists N : nat,
        forall n : nat,
        n >= N ->
        agrees_on_list (seq n) P S.
        
    End Definitions.
    
    (** *** Standard Sequences *)
    Section StandardSequences.
      Context {Alpha : AlphaType}.
      
      (** The constant sequence *)
      Definition constant_sequence (P : Alphacarrier -> Prop) : predicate_sequence :=
        fun n => P.
      
      (** Oscillating between two predicates *)
      Definition oscillating_sequence : predicate_sequence :=
        fun n => if Nat.even n then (fun _ => True) else omega_veil.
      
      (** A sequence that "shrinks" by requiring membership in smaller sets *)
      Definition shrinking_sequence (base : Alphacarrier -> Prop) : predicate_sequence :=
        fun n => fun a => base a /\ 
          exists (witness_list : list Alphacarrier), 
          length witness_list <= n /\ 
          In a witness_list.
      
      (** Alternating between predicates based on a pattern *)
      Definition alternating_sequence (P Q : Alphacarrier -> Prop) : predicate_sequence :=
        fun n => if Nat.even n then P else Q.
        
    End StandardSequences.
    
    (** *** Convergence Properties *)
    Section Properties.
      Context {Alpha : AlphaType}.
      
      (** Constant sequences converge to their constant value *)
      Theorem constant_converges :
        forall P, converges_to (constant_sequence P) P.
      Proof.
        intros P witnesses.
        exists 0.
        intros n Hn a Ha.
        unfold constant_sequence, agrees_at.
        reflexivity.
      Qed.
      
      (** Convergence is unique when it exists *)
      Theorem convergence_unique :
        forall seq P Q,
        converges_to seq P ->
        converges_to seq Q ->
        forall a, P a <-> Q a.
      Proof.
        intros seq P Q HP HQ a.
        destruct (HP [a]) as [NP HNP].
        destruct (HQ [a]) as [NQ HNQ].
        pose (N := max NP NQ).
        assert (HNP' : agrees_at (seq N) P a).
        { apply HNP. unfold N. apply Nat.le_max_l. left. reflexivity. }
        assert (HNQ' : agrees_at (seq N) Q a).
        { apply HNQ. unfold N. apply Nat.le_max_r. left. reflexivity. }
        unfold agrees_at in *.
        split; intro H.
        - apply HNQ'. apply HNP'. exact H.
        - apply HNP'. apply HNQ'. exact H.
      Qed.
      
      (** Helper lemmas for oscillating sequence analysis *)
      Section OscillatingAnalysis.
        
        Lemma oscillating_at_even :
          forall n a,
          Nat.even n = true ->
          oscillating_sequence n a <-> True.
        Proof.
          intros n a Heven.
          unfold oscillating_sequence.
          rewrite Heven.
          split; intro; exact I.
        Qed.
        
        Lemma oscillating_at_odd :
          forall n a,
          Nat.even n = false ->
          oscillating_sequence n a <-> omega_veil a.
        Proof.
          intros n a Hodd.
          unfold oscillating_sequence.
          rewrite Hodd.
          reflexivity.
        Qed.
        
        Lemma even_plus_one_odd :
          forall n,
          Nat.even n = true ->
          Nat.even (n + 1) = false.
        Proof.
          intros n Heven.
          rewrite Nat.even_add.
          rewrite Heven.
          reflexivity.
        Qed.
        
      End OscillatingAnalysis.
      
      (** The oscillating sequence cannot converge *)
      Theorem oscillating_not_convergent :
        ~ exists P, converges_to oscillating_sequence P.
      Proof.
        intros [P Hconv].
        destruct alpha_not_empty as [a0 _].
        destruct (Hconv [a0]) as [N HN].
        
        (* Find a large even number >= N *)
        pose (E := 2 * N).
        assert (HE_even : Nat.even E = true).
        { unfold E. rewrite Nat.even_mul. reflexivity. }
        assert (HE_ge : E >= N).
        { unfold E. rewrite <- (Nat.mul_1_l N) at 2. 
          apply Nat.mul_le_mono_r. apply Nat.le_succ_diag_r. }
        
        (* At position E: oscillating_sequence E a0 <-> True *)
        assert (H_in : In a0 [a0]) by (left; reflexivity).
        pose proof (HN_E := HN E HE_ge a0 H_in).
        (* HN_E : agrees_at (oscillating_sequence E) P a0 *)
        (* which means: oscillating_sequence E a0 <-> P a0 *)
        
        (* Use oscillating_at_even to get oscillating_sequence E a0 <-> True *)
        pose proof (H_E_true := oscillating_at_even E a0 HE_even).
        (* H_E_true : oscillating_sequence E a0 <-> True *)
        
        (* At position E+1: oscillating_sequence (E+1) a0 <-> omega_veil a0 *)
        assert (HE1_ge : E + 1 >= N).
        { unfold ge. apply Nat.le_trans with E; [exact HE_ge | apply Nat.le_add_r]. }
        pose proof (HN_E1 := HN (E + 1) HE1_ge a0 H_in).
        (* HN_E1 : agrees_at (oscillating_sequence (E + 1)) P a0 *)
        (* which means: oscillating_sequence (E + 1) a0 <-> P a0 *)
        
        (* Use oscillating_at_odd to get oscillating_sequence (E+1) a0 <-> omega_veil a0 *)
        assert (HE1_odd : Nat.even (E + 1) = false).
        { apply even_plus_one_odd. exact HE_even. }
        pose proof (H_E1_omega := oscillating_at_odd (E + 1) a0 HE1_odd).
        (* H_E1_omega : oscillating_sequence (E + 1) a0 <-> omega_veil a0 *)
        
        (* Now we can derive the contradiction:
           From HN_E and H_E_true: P a0 <-> True
           From HN_E1 and H_E1_omega: P a0 <-> omega_veil a0
           Therefore: True <-> omega_veil a0 *)
        
        (* P a0 holds because it's equivalent to True *)
        assert (P a0).
        { apply HN_E. apply H_E_true. exact I. }
        
        (* But P a0 is also equivalent to omega_veil a0 *)
        assert (omega_veil a0).
        { apply H_E1_omega. apply HN_E1. exact H. }
        
        (* This contradicts the fact that omega_veil has no witnesses *)
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a0 H0).
      Qed.
      
      (** Helper: strictly increasing functions eventually dominate any constant *)
      Lemma strictly_increasing_dominates :
        forall (f : nat -> nat),
        (forall n, f n < f (S n)) ->
        forall n, f n >= n.
      Proof.
        intros f Hf n.
        induction n.
        - apply Nat.le_0_l.
        - unfold ge in *.
          specialize (Hf n).
          unfold lt in Hf.
          apply Nat.le_trans with (S (f n)).
          + apply le_n_S. exact IHn.
          + exact Hf.
      Qed.
      
      (** Subsequence convergence *)
      Theorem subsequence_converges :
        forall seq P (f : nat -> nat),
        (forall n, f n < f (S n)) ->  (* f is strictly increasing *)
        converges_to seq P ->
        converges_to (fun n => seq (f n)) P.
      Proof.
        intros seq P f Hf Hconv witnesses.
        destruct (Hconv witnesses) as [N HN].
        exists N.
        intros n Hn a Ha.
        apply HN; [|exact Ha].
        unfold ge.
        apply Nat.le_trans with n.
        - exact Hn.
        - apply strictly_increasing_dominates. exact Hf.
      Qed.
      
    End Properties.
  End Convergence.
  
  (* ================================================================ *)
  (** ** Continuity Theory
      
      We develop a notion of continuity for functions between predicate spaces.
      A function is continuous if it preserves convergence. *)
  Module Continuity.
    Import Core Convergence.
    
    (** *** Basic Definitions *)
    Section Definitions.
      Context {Alpha : AlphaType}.
      
      (** A transformation is continuous if it preserves convergence *)
      Definition continuous (F : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop)) : Prop :=
        forall (seq : predicate_sequence) (P : Alphacarrier -> Prop),
        converges_to seq P ->
        converges_to (fun n => F (seq n)) (F P).
      
      (** Uniform continuity on a specific set *)
      Definition uniformly_continuous_on (F : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop))
                                        (S : list Alphacarrier) : Prop :=
        forall (seq : predicate_sequence) (P : Alphacarrier -> Prop),
        converges_uniformly_on seq P S ->
        converges_uniformly_on (fun n => F (seq n)) (F P) S.
        
    End Definitions.
    
    (** *** Basic Operations *)
    Section BasicOperations.
      Context {Alpha : AlphaType}.
      
      (** Negation operation *)
      Definition pred_neg (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        fun a => ~ P a.
      
      (** Binary operations *)
      Definition pred_and (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        fun a => P a /\ Q a.
      
      Definition pred_or (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        fun a => P a \/ Q a.
      
      Definition pred_impl (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
        fun a => P a -> Q a.
      
      (** Identity is trivially continuous *)
      Definition pred_id (P : Alphacarrier -> Prop) : Alphacarrier -> Prop := P.
      
    End BasicOperations.
    
    (** *** Continuity Results *)
    Section ContinuityResults.
      Context {Alpha : AlphaType}.
      
      (** Identity is continuous *)
      Theorem id_continuous : continuous pred_id.
      Proof.
        unfold continuous, pred_id.
        intros seq P Hconv.
        exact Hconv.
      Qed.
      
      (** Negation is continuous *)
      Theorem negation_continuous : continuous pred_neg.
      Proof.
        unfold continuous, converges_to.
        intros seq P Hconv witnesses.
        destruct (Hconv witnesses) as [N HN].
        exists N.
        intros n Hn a Ha.
        specialize (HN n Hn a Ha).
        unfold pred_neg, agrees_at in *.
        split; intro H.
        - intro HPa. apply H. apply HN. exact HPa.
        - intro Hseq. apply H. apply HN. exact Hseq.
      Qed.
      
      (** Conjunction is continuous in the first argument *)
      Theorem and_continuous_left :
        forall Q, continuous (fun P => pred_and P Q).
      Proof.
        intros Q.
        unfold continuous, converges_to.
        intros seq P Hconv witnesses.
        destruct (Hconv witnesses) as [N HN].
        exists N.
        intros n Hn a Ha.
        specialize (HN n Hn a Ha).
        unfold pred_and, agrees_at in *.
        split; intros [H1 H2].
        - split. apply HN. exact H1. exact H2.
        - split. apply HN. exact H1. exact H2.
      Qed.
      
      (** Disjunction is continuous in the first argument *)
      Theorem or_continuous_left :
        forall Q, continuous (fun P => pred_or P Q).
      Proof.
        intros Q.
        unfold continuous, converges_to.
        intros seq P Hconv witnesses.
        destruct (Hconv witnesses) as [N HN].
        exists N.
        intros n Hn a Ha.
        specialize (HN n Hn a Ha).
        unfold pred_or, agrees_at in *.
        split; intros [H | H].
        - left. apply HN. exact H.
        - right. exact H.
        - left. apply HN. exact H.  
        - right. exact H.
      Qed.
      
      (** Composition preserves continuity *)
      Theorem continuous_compose :
        forall F G,
        continuous F ->
        continuous G ->
        continuous (fun P => F (G P)).
      Proof.
        intros F G HF HG.
        unfold continuous in *.
        intros seq P Hconv.
        apply HF.
        apply HG.
        exact Hconv.
      Qed.
      
      (** Constant functions are continuous *)
      Theorem constant_function_continuous :
        forall Q, continuous (fun P => Q).
      Proof.
        intros Q.
        unfold continuous, converges_to.
        intros seq P Hconv witnesses.
        exists 0.
        intros n Hn a Ha.
        unfold agrees_at.
        reflexivity.
      Qed.
      
    End ContinuityResults.
    
    (** *** Advanced Properties *)
    Section AdvancedProperties.
      Context {Alpha : AlphaType}.
      
      (** If F is continuous and maps impossibles to impossibles,
          then F preserves approach to impossibility *)
      Theorem continuous_preserves_approach_impossible :
        forall F,
        continuous F ->
        Is_Impossible (F omega_veil) ->
        forall seq,
        approaches_impossible seq ->
        approaches_impossible (fun n => F (seq n)).
      Proof.
        intros F Hcont Himp seq Happ.
        unfold approaches_impossible in *.
        (* seq converges to omega_veil, so F(seq) converges to F(omega_veil) *)
        apply Hcont in Happ.
        (* But F(omega_veil) is impossible, so F(omega_veil) = omega_veil pointwise *)
        unfold converges_to in *.
        intros witnesses.
        destruct (Happ witnesses) as [N HN].
        exists N.
        intros n Hn a Ha.
        specialize (HN n Hn a Ha).
        unfold agrees_at in *.
        (* HN : F (seq n) a <-> F omega_veil a *)
        (* We need: F (seq n) a <-> omega_veil a *)
        (* Since Himp : Is_Impossible (F omega_veil), we have F omega_veil a <-> omega_veil a *)
        unfold Is_Impossible in Himp.
        specialize (Himp a).
        (* Himp : F omega_veil a <-> omega_veil a *)
        split.
        - intro H. 
          apply Himp.
          apply HN.
          exact H.
        - intro H.
          apply HN.
          apply Himp.
          exact H.
      Qed.
      
    End AdvancedProperties.
  End Continuity.
  
  (* ================================================================ *)
  (** ** Observable Differences
      
      A constructive approach to detecting when predicates differ.
      This provides a computational way to witness disagreements. *)
  Module Observability.
    Import Core.
    
    Section ObservableDefinitions.
      Context {Alpha : AlphaType}.
      
      (** Constructive evidence that two predicates differ at a point *)
      Inductive observable_diff (P Q : Alphacarrier -> Prop) : Alphacarrier -> Type :=
        | diff_PQ : forall a, P a -> ~ Q a -> observable_diff P Q a
        | diff_QP : forall a, ~ P a -> Q a -> observable_diff P Q a.
      
      (** No observable differences on a witness set *)
      Definition no_observable_diffs (P Q : Alphacarrier -> Prop) 
                                    (witnesses : list Alphacarrier) : Prop :=
        forall a, In a witnesses -> 
          (P a -> Q a) /\ (Q a -> P a).
      
      (** Observable difference is symmetric *)
      Definition swap_diff {P Q : Alphacarrier -> Prop} {a : Alphacarrier}
                        (d : observable_diff P Q a) : observable_diff Q P a :=
      match d with
      | diff_PQ _ _ a pa nqa => diff_QP Q P a nqa pa
      | diff_QP _ _ a npa qa => diff_PQ Q P a qa npa
      end.
      
    End ObservableDefinitions.
    
    Section ObservableProperties.
      Context {Alpha : AlphaType}.
      
      (** No observable differences is equivalent to agreement *)
      Theorem no_diffs_iff_agrees :
        forall P Q witnesses,
        no_observable_diffs P Q witnesses <-> agrees_on_list P Q witnesses.
      Proof.
        intros P Q witnesses.
        unfold no_observable_diffs, agrees_on_list, agrees_at.
        split.
        - intros H a Ha.
          specialize (H a Ha).
          split; apply H.
        - intros H a Ha.
          specialize (H a Ha).
          split; apply H.
      Qed.
      
      (** If we can observe a difference, the predicates don't agree there *)
      Theorem observable_diff_not_agrees :
        forall P Q a,
        observable_diff P Q a ->
        ~ agrees_at P Q a.
      Proof.
        intros P Q a Hdiff.
        unfold agrees_at.
        intro H.
        destruct Hdiff.
        - apply n. apply H. exact p.
        - apply n. apply H. exact q.
      Qed.
      
      (** Decidable equality gives decidable observable differences *)
      Section WithDecidability.
        Hypothesis P_decidable : forall (P : Alphacarrier -> Prop) a, {P a} + {~ P a}.
        
        Definition decide_diff (P Q : Alphacarrier -> Prop) (a : Alphacarrier) :
          (observable_diff P Q a) + (agrees_at P Q a).
        Proof.
          destruct (P_decidable P a) as [HPa | HnPa].
          - destruct (P_decidable Q a) as [HQa | HnQa].
            + right. unfold agrees_at. split; intro; assumption.
            + left. exact (diff_PQ P Q a HPa HnQa).
          - destruct (P_decidable Q a) as [HQa | HnQa].
            + left. exact (diff_QP P Q a HnPa HQa).
            + right. unfold agrees_at. split; intro H; contradiction.
        Defined.
        
      End WithDecidability.
      
    End ObservableProperties.
  End Observability.
  
  (* ================================================================ *)
  (** ** Paths in Predicate Space
      
      We explore paths between predicates - continuous deformations
      from one predicate to another. *)
  Module Paths.
    Import Core Convergence.
    
    Section PathDefinitions.
      Context {Alpha : AlphaType}.
      
      (** A path is just a predicate sequence *)
      Definition predicate_path := predicate_sequence.
      
      (** A path connects P to Q if it starts at P and converges to Q *)
      Definition path_from_to (path : predicate_path) (P Q : Alphacarrier -> Prop) : Prop :=
        path 0 = P /\
        converges_to path Q.
      
      (** The reverse of a path (may not converge) *)
      Definition reverse_path (path : predicate_path) (length : nat) : predicate_path :=
        fun n => if n <=? length then path (length - n) else path 0.
      
      (** Concatenation of paths *)
      Definition concat_paths (path1 path2 : predicate_path) (length1 : nat) : predicate_path :=
        fun n => if n <=? length1 then path1 n else path2 (n - length1).
        
    End PathDefinitions.
    
    Section StandardPaths.
      Context {Alpha : AlphaType}.
      
      (** The trivial path stays at one predicate *)
      Definition trivial_path (P : Alphacarrier -> Prop) : predicate_path :=
        constant_sequence P.
      
      (** Linear interpolation (in a discrete sense) *)
      Definition linear_path (P Q : Alphacarrier -> Prop) (steps : nat) : predicate_path :=
        fun n => if n <? steps then P else Q.
      
      (** A path that gradually "fades" a predicate *)
      Definition fade_path (P : Alphacarrier -> Prop) : predicate_path :=
        fun n => fun a => P a /\ 
          exists (proof_size : nat), proof_size <= n.
          
    End StandardPaths.
    
    Section PathProperties.
      Context {Alpha : AlphaType}.
      
      (** The trivial path connects P to itself *)
      Theorem trivial_path_connects :
        forall P, path_from_to (trivial_path P) P P.
      Proof.
        intro P.
        split.
        - unfold trivial_path, constant_sequence. reflexivity.
        - apply constant_converges.
      Qed.
      
      (** Linear path starts at P when steps > 0 *)
    Lemma linear_path_start :
      forall P Q steps,
      linear_path P Q steps 0 = if steps =? 0 then Q else P.
    Proof.
      intros P Q steps.
      unfold linear_path.
      destruct steps.
      - simpl. reflexivity.
      - simpl. reflexivity.
    Qed.

    (** The degenerate case: steps = 0 means we're already at Q *)
    Theorem linear_path_connects_degenerate :
      forall P Q,
      path_from_to (linear_path P Q 0) Q Q.
    Proof.
      intros P Q.
      split.
      - unfold linear_path. simpl. reflexivity.
      - unfold converges_to.
        intros witnesses.
        exists 0.
        intros n Hn a Ha.
        unfold linear_path, agrees_at.
        simpl. reflexivity.
    Qed.

    (** The normal case: steps > 0 *)
    Theorem linear_path_connects_positive :
      forall P Q steps,
      steps > 0 ->
      path_from_to (linear_path P Q steps) P Q.
    Proof.
      intros P Q steps Hsteps.
      split.
      - unfold linear_path.
        assert (0 <? steps = true).
        { apply Nat.ltb_lt. exact Hsteps. }
        simpl. rewrite H. reflexivity.
      - unfold converges_to, linear_path.
        intros witnesses.
        exists steps.
        intros n Hn a Ha.
        assert (~ n < steps).
        { intro H. unfold ge in Hn. 
          apply Nat.lt_nge in H. contradiction. }
        rewrite <- Nat.ltb_nlt in H.
        rewrite H.
        unfold agrees_at.
        reflexivity.
    Qed.

    (** We can combine these into a more general statement *)
    Theorem linear_path_characterization :
      forall P Q steps,
      (steps = 0 -> path_from_to (linear_path P Q steps) Q Q) /\
      (steps > 0 -> path_from_to (linear_path P Q steps) P Q).
    Proof.
      intros P Q steps.
      split.
      - intro H. subst. apply linear_path_connects_degenerate.
      - apply linear_path_connects_positive.
    Qed.

    (** At any point before steps, we're at P *)
    Lemma linear_path_before_steps :
      forall P Q steps n,
      n < steps ->
      linear_path P Q steps n = P.
    Proof.
      intros P Q steps n Hn.
      unfold linear_path.
      apply Nat.ltb_lt in Hn.
      rewrite Hn. reflexivity.
    Qed.

    (** At any point after steps, we're at Q *)
    Lemma linear_path_after_steps :
      forall P Q steps n,
      n >= steps ->
      linear_path P Q steps n = Q.
    Proof.
      intros P Q steps n Hn.
      unfold linear_path.
      assert (~ n < steps).
      { intro H. unfold ge in Hn. apply Nat.lt_nge in H. contradiction. }
      rewrite <- Nat.ltb_nlt in H.
      rewrite H. reflexivity.
    Qed.

    (** Path concatenation preserves connectivity under conditions *)
    Theorem concat_paths_connects :
      forall path1 path2 P Q R length1,
      path_from_to path1 P Q ->
      path_from_to path2 Q R ->
      path1 length1 = Q ->
      path_from_to (concat_paths path1 path2 length1) P R.
    Proof.
      intros path1 path2 P Q R length1 [H1start H1conv] [H2start H2conv] Hmid.
      split.
      - (* concat starts at path1 0 = P *)
        unfold concat_paths. simpl.
        destruct (0 <=? length1) eqn:H.
        + exact H1start.
        + (* Impossible: 0 <= any nat *)
          apply Nat.leb_nle in H. lia.
          
      - (* Show convergence to R *)
        unfold converges_to in *.
        intros witnesses.
        
        (* Get convergence point for path2 *)
        destruct (H2conv witnesses) as [N2 HN2].
        
        (* Choose N large enough so we're always in path2 territory *)
        exists (S length1 + N2).
        intros n Hn a Ha.
        
        unfold concat_paths, agrees_at.
        
        (* Since n >= S length1 + N2, we have n > length1 *)
        assert (Hgt : n <=? length1 = false).
        { apply Nat.leb_nle. unfold ge in Hn. lia. }
        rewrite Hgt.
        
        (* Apply convergence of path2 *)
        apply HN2.
        + (* n - length1 >= N2 *)
          unfold ge in *. lia.
        + (* a ∈ witnesses *)
          exact Ha.
    Qed.
      
    End PathProperties.
  End Paths.
  
  (* ================================================================ *)
  (** ** Limits and Fixed Points
      
      Advanced concepts including limits of sequences and fixed points
      of continuous transformations. *)
  Module Limits.
    Import Core Convergence Continuity.
    
    Section LimitDefinitions.
      Context {Alpha : AlphaType}.
      
      (** The limit of a convergent sequence (when it exists) *)
      Definition limit_of (seq : predicate_sequence) : (Alphacarrier -> Prop) -> Prop :=
        converges_to seq.
      
      (** A fixed point of a transformation *)
      Definition is_fixed_point (F : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop))
                               (P : Alphacarrier -> Prop) : Prop :=
        forall a, F P a <-> P a.
      
      (** The sequence of iterates of F starting from P *)
      Fixpoint iterate (F : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop))
                      (P : Alphacarrier -> Prop) (n : nat) : Alphacarrier -> Prop :=
        match n with
        | 0 => P
        | S n' => F (iterate F P n')
        end.
        
    End LimitDefinitions.
    
    Section FixedPointProperties.
      Context {Alpha : AlphaType}.
      
      (** If F is continuous and the iterates converge, the limit is a fixed point *)
      Theorem continuous_limit_fixed :
        forall F P Q,
        continuous F ->
        converges_to (iterate F P) Q ->
        is_fixed_point F Q.
      Proof.
        intros F P Q Hcont Hconv.
        unfold is_fixed_point.
        intro a.
        
        (* F(lim seq) = lim F(seq) by continuity *)
        assert (converges_to (fun n => F (iterate F P n)) (F Q)).
        { apply Hcont. exact Hconv. }
        
        (* But F(iterate n) = iterate (n+1) *)
        assert (forall n, F (iterate F P n) = iterate F P (S n)).
        { intro n. reflexivity. }
        
        (* So the shifted sequence also converges to Q *)
        assert (converges_to (fun n => iterate F P (S n)) Q).
        { apply subsequence_converges with (f := S); auto. }
        
        (* By uniqueness of limits, F Q = Q *)
        pose proof (Huniq := convergence_unique (fun n => iterate F P (S n)) (F Q) Q).
        assert (forall a, F Q a <-> Q a).
        { intro a'. apply Huniq; assumption. }
        exact (H2 a).
      Qed.
      
      (** Banach-like fixed point theorem for contractive maps *)
      (* This would require a notion of distance, which we don't have yet *)
      
    End FixedPointProperties.
  End Limits.
  
  (* ================================================================ *)
  (** ** Metric Structure
      
      While we don't have a true metric, we can define pseudo-metrics
      based on finite witness sets. *)
  Module Metrics.
    Import Core Convergence Observability.
    
    Section PseudoMetrics.
      Context {Alpha : AlphaType}.
      
      (** Count disagreements when we have decidability *)
      Section WithDecidability.
        Hypothesis P_decidable : forall (P : Alphacarrier -> Prop) a, {P a} + {~ P a}.
        
        (** The size of the disagreement set (when finite) *)
        Definition disagreement_size (P Q : Alphacarrier -> Prop) 
                                    (witnesses : list Alphacarrier) : nat :=
          length (filter (fun a => 
            match P_decidable P a, P_decidable Q a with
            | left _, left _ => false   (* both true *)
            | right _, right _ => false (* both false *)
            | _, _ => true              (* disagree *)
            end) witnesses).
        
        (** A sequence is Cauchy-like if disagreements eventually vanish *)
        Definition is_cauchy_like (seq : predicate_sequence) : Prop :=
          forall witnesses : list Alphacarrier,
          forall ε : nat,
          exists N : nat,
          forall m n : nat,
          m >= N -> n >= N ->
          disagreement_size (seq m) (seq n) witnesses <= ε.
        
        (** Distance to omega_veil is special - count witnesses *)
        Definition distance_to_impossible (P : Alphacarrier -> Prop) 
                                         (witnesses : list Alphacarrier) : nat :=
          length (filter (fun a => 
            match P_decidable P a with
            | left _ => true   (* P has a witness here *)
            | right _ => false (* P fails here, like omega_veil *)
            end) witnesses).
            
      End WithDecidability.
        
    End PseudoMetrics.
  End Metrics.
  
  (* ================================================================ *)
  (** ** Integration with ImpossibilityAlgebra
      
      Connecting the calculus concepts with the algebraic structure. *)
  Module AlgebraicConnections.
    Import Core Convergence Continuity ImpossibilityAlgebra.Operations.
    
    Section Connections.
      Context {Alpha : AlphaType}.
      
      (** Impossibility is preserved by continuous functions that preserve logic *)
      Theorem continuous_preserves_impossibility :
        forall F,
        continuous F ->
        (forall P Q a, F (fun x => P x /\ Q x) a <-> F P a /\ F Q a) ->
        (forall P a, F P a -> exists a', P a') ->  (* F doesn't create witnesses *)
        forall P, Is_Impossible P -> Is_Impossible (F P).
      Proof.
        intros F Hcont Hlogic Hwitness P Himp.
        unfold Is_Impossible.
        intro a.
        split.
        - (* F P a -> omega_veil a *)
          intro HFPa.
          (* F P has a witness at a, so P must have a witness somewhere *)
          destruct (Hwitness P a HFPa) as [a' HPa'].
          (* But P is impossible, so P a' <-> omega_veil a' *)
          apply Himp in HPa'.
          (* omega_veil has no witnesses - contradiction *)
          exfalso.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses a' HPa').
        - (* omega_veil a -> F P a *)
          intro Hveil.
          exfalso.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
      Qed.
      
      (** The space of impossible predicates is "closed" under limits *)
      Theorem impossible_closed_under_limits :
        forall seq P,
        (forall n, Is_Impossible (seq n)) ->
        converges_to seq P ->
        Is_Impossible P.
      Proof.
        intros seq P Himp_seq Hconv.
        unfold Is_Impossible.
        intro a.
        split.
        - intro HPa.
          (* P a holds. By convergence, seq n eventually agrees with P at a. *)
          destruct (Hconv [a]) as [N HN].
          specialize (HN N (Nat.le_refl N) a (or_introl eq_refl)).
          unfold agrees_at in HN.
          (* HN : seq N a <-> P a *)
          (* So seq N a holds *)
          assert (Hseq : seq N a) by (apply HN; exact HPa).
          (* But seq N is impossible, so seq N a <-> omega_veil a *)
          specialize (Himp_seq N a).
          apply Himp_seq. exact Hseq.
        - intro Hveil.
          exfalso.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
      Qed.
      
    End Connections.
  End AlgebraicConnections.
  
  (** Note: Several proofs are admitted as they require additional machinery
      or would be quite lengthy. These serve as placeholders for future work. *)
  
End ImpossibilityCalculus.