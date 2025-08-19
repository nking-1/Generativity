Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
Import ListNotations.


(** * ZFC in ClassicalAlphaType
    
    This module shows that ZFC set theory naturally lives inside ClassicalAlphaType,
    with the empty set being exactly classical_veil - the one impossible predicate. *)

Module ZFC.

  (** ** Basic Definitions
      
      Sets are predicates, membership is predicate application *)
  Module Basic.
    Section BasicDefs.
      Context {H_alpha: ClassicalAlphaType}.
      
      (* Sets are just predicates *)
      Definition ZSet := ClassicalAlphaProperties.Helpers.AlphaPred.
      
      (* Membership is predicate application *)
      Definition In (x : Alphacarrier) (A : ZSet) : Prop := A x.
      
      (* Set equality via extensionality *)
      Definition set_eq (A B : ZSet) : Prop := 
        ClassicalAlphaProperties.Predicates.pred_equiv A B.
      
      (* Axiom 1: Extensionality (but it's just pred_equiv!) *)
      Theorem extensionality : forall A B : ZSet,
        (forall x, In x A <-> In x B) <-> set_eq A B.
      Proof.
        intros A B.
        unfold set_eq, ClassicalAlphaProperties.Predicates.pred_equiv, In.
        split; intro H; exact H.
      Qed.
      
    End BasicDefs.
  End Basic.

  (** ** Fundamental Sets
      
      The empty set (classical_veil) and basic constructions *)
  Module Fundamental.
    Section FundamentalSets.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      
      (* The empty set is classical_veil! *)
      Definition Empty : ZSet := classical_veil.
      
      Theorem empty_set_exists : exists E : ZSet, forall x, ~ In x E.
      Proof.
        exists Empty.
        intros x.
        unfold In, Empty.
        apply ClassicalAlphaProperties.Core.classical_veil_is_impossible.
      Qed.
      
      (* Singleton sets *)
      Definition singleton (a : Alphacarrier) : ZSet :=
        fun x => x = a.
      
      Theorem singleton_spec : forall a x,
        In x (singleton a) <-> x = a.
      Proof.
        intros a x.
        unfold In, singleton.
        split; intro H; exact H.
      Qed.
      
      (* Pairing *)
      Definition pair (a b : Alphacarrier) : ZSet :=
        fun x => x = a \/ x = b.
      
      Theorem pair_spec : forall a b x,
        In x (pair a b) <-> (x = a \/ x = b).
      Proof.
        intros a b x.
        unfold In, pair.
        split; intro H; exact H.
      Qed.
      
      (* Basic non-emptiness results *)
      Theorem singleton_not_empty : forall a,
        ~ (set_eq (singleton a) Empty).
      Proof.
        intros a H_eq.
        assert (In a (singleton a)) by (apply singleton_spec; reflexivity).
        assert (In a Empty) by (apply H_eq; exact H).
        unfold In, Empty in H0.
        apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible a).
        exact H0.
      Qed.

    End FundamentalSets.
  End Fundamental.

  (** ** Set Operations
      
      Union, intersection, complement, etc. *)
  Module Operations.
    Section SetOperations.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      
      (* Define subset relation *)
      Definition subset (A B : ZSet) : Prop :=
        forall x, In x A -> In x B.
      
      (* Binary union *)
      Definition union2 (A B : ZSet) : ZSet :=
        fun x => In x A \/ In x B.
      
      Theorem union2_spec : forall A B x,
        In x (union2 A B) <-> (In x A \/ In x B).
      Proof.
        intros A B x.
        unfold In, union2.
        split; intro H; exact H.
      Qed.
      
      (* Intersection *)
      Definition inter2 (A B : ZSet) : ZSet :=
        fun x => In x A /\ In x B.
      
      Theorem inter2_spec : forall A B x,
        In x (inter2 A B) <-> (In x A /\ In x B).
      Proof.
        intros A B x.
        unfold In, inter2.
        split; intro H; exact H.
      Qed.
      
      (* Complement *)
      Definition compl (A : ZSet) : ZSet :=
        fun x => ~ In x A.
      
      (* The universal set *)
      Definition Universal : ZSet := 
        ClassicalAlphaProperties.Helpers.the_necessary.
      
      Theorem universal_contains_all : forall x,
        In x Universal.
      Proof.
        intros x.
        unfold In, Universal, ClassicalAlphaProperties.Helpers.the_necessary.
        apply ClassicalAlphaProperties.Core.classical_veil_is_impossible.
      Qed.
    End SetOperations.
  End Operations.

  (** ** Set Algebra
      
      Basic theorems about set operations *)
  Module Algebra.
    Section SetAlgebra.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      Import Operations.
      
      Theorem union_empty_left : forall A,
        set_eq (union2 Empty A) A.
      Proof.
        intros A.
        unfold set_eq, ClassicalAlphaProperties.Predicates.pred_equiv.
        intros x.
        split.
        - intros [H_empty | H_A].
          + unfold In, Empty in H_empty.
            exfalso.
            apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible x).
            exact H_empty.
          + exact H_A.
        - intros H_A.
          right. exact H_A.
      Qed.
      
      (* De Morgan's laws *)
      Theorem de_morgan_union : forall A B,
        set_eq (compl (union2 A B)) (inter2 (compl A) (compl B)).
      Proof.
        intros A B.
        unfold set_eq, ClassicalAlphaProperties.Predicates.pred_equiv.
        intros x.
        unfold In, compl, union2, inter2.
        split.
        - intros H_not_union.
          split.
          + intros H_A. 
            apply H_not_union.
            left. exact H_A.
          + intros H_B.
            apply H_not_union.
            right. exact H_B.
        - intros [H_not_A H_not_B] [H_A | H_B].
          + exact (H_not_A H_A).
          + exact (H_not_B H_B).
      Qed.
    End SetAlgebra.
  End Algebra.

  (** ** Set Codes
      
      Encoding sets as elements for higher-order constructions *)
  Module Codes.
    Section SetCodes.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      
      (* Axiomatize that some elements can represent sets *)
      Axiom is_set_code : Alphacarrier -> Prop.
      Axiom set_decode : Alphacarrier -> ZSet.
      
      (* set_decode is only meaningful for set codes *)
      Axiom decode_only_codes : forall x,
        ~ is_set_code x -> set_eq (set_decode x) Empty.
      
      (* For any predicate that's "set-like", there's a code for it *)
      Axiom set_encode_exists : forall (S : ZSet), 
        (exists a, In a S) \/ (forall a, ~ In a S) ->
        exists x, is_set_code x /\ set_eq (set_decode x) S.
      
      (* The membership relation for coded sets *)
      Definition mem (a b : Alphacarrier) : Prop :=
        is_set_code b /\ In a (set_decode b).
      
      (* Direct axiomatization of important set codes *)
      Axiom empty_code : Alphacarrier.
      Axiom empty_code_spec : 
        is_set_code empty_code /\ set_eq (set_decode empty_code) Empty.
      
      Axiom singleton_code : Alphacarrier -> Alphacarrier.
      Axiom singleton_code_spec : forall a,
        is_set_code (singleton_code a) /\ 
        set_eq (set_decode (singleton_code a)) (singleton a).
      
      Axiom pair_code : Alphacarrier -> Alphacarrier -> Alphacarrier.
      Axiom pair_code_spec : forall a b,
        is_set_code (pair_code a b) /\ 
        set_eq (set_decode (pair_code a b)) (pair a b).
      
      (* Helper lemmas *)
      Lemma not_mem_empty : forall x, ~ mem x empty_code.
      Proof.
        intros x [Hcode Hin].
        destruct empty_code_spec as [_ Hdecode].
        apply Hdecode in Hin.
        unfold In, Empty in Hin.
        exact (ClassicalAlphaProperties.Core.classical_veil_is_impossible x Hin).
      Qed.
    End SetCodes.
  End Codes.

  (** ** Axioms
      
      The standard ZFC axioms in our framework *)
  Module Axioms.
    Section ZFCAxioms.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      Import Operations.
      Import Codes.
      
      (* Union axiom *)
      Definition is_union_of (F union_set : Alphacarrier) : Prop :=
        is_set_code F /\ is_set_code union_set /\
        forall x, mem x union_set <-> exists Y, mem Y F /\ mem x Y.
      
      Axiom union_exists : forall F,
        is_set_code F ->
        exists U, is_union_of F U.
      
      (* Separation axiom schema *)
      Axiom separation : forall A (P : Alphacarrier -> Prop),
        is_set_code A ->
        exists B, is_set_code B /\
          forall x, mem x B <-> (mem x A /\ P x).
      
      (* Axiom of infinity *)
      Definition is_successor (x sx : Alphacarrier) : Prop :=
        is_set_code x /\ is_set_code sx /\
        forall y, mem y sx <-> (mem y x \/ y = x).
      
      Definition is_inductive (I : Alphacarrier) : Prop :=
        is_set_code I /\
        (exists e, is_set_code e /\ (forall x, ~ mem x e) /\ mem e I) /\
        (forall x, mem x I -> exists sx, is_successor x sx /\ mem sx I).
      
      Axiom infinity : exists I, is_inductive I.
      
      (* Power set axiom *)
      Definition encodes_subset (x A : Alphacarrier) : Prop :=
        is_set_code x /\ is_set_code A /\
        forall y, mem y x -> mem y A.
      
      Definition is_powerset (A ps : Alphacarrier) : Prop :=
        is_set_code A /\ is_set_code ps /\
        forall x, mem x ps <-> encodes_subset x A.
      
      Axiom powerset_exists : forall A,
        is_set_code A -> exists ps, is_powerset A ps.
      
      (* Replacement axiom *)
      Definition is_functional (R : Alphacarrier -> Alphacarrier -> Prop) : Prop :=
        forall x y z, R x y -> R x z -> y = z.
      
      Axiom replacement : forall A (R : Alphacarrier -> Alphacarrier -> Prop),
        is_set_code A ->
        is_functional R ->
        exists B, is_set_code B /\
          forall y, mem y B <-> exists x, mem x A /\ R x y.
      
      (* Foundation axiom *)
      Axiom foundation : forall A,
        is_set_code A ->
        (exists x, mem x A) ->
        exists x, mem x A /\ forall y, mem y x -> ~ mem y A.
      
      (* Axiom of choice *)
      Definition is_family_of_sets (F : Alphacarrier) : Prop :=
        is_set_code F /\ forall x, mem x F -> is_set_code x.
      
      Definition is_choice_function (F f : Alphacarrier) : Prop :=
        is_family_of_sets F /\ is_set_code f /\
        forall A, mem A F -> 
          (exists a, mem a A) ->
          exists a, mem a A /\ mem (pair_code A a) f.
      
      Axiom choice : forall F,
        is_family_of_sets F ->
        (forall A, is_set_code A -> In A (set_decode F) -> 
          exists a, is_set_code a /\ In a (set_decode A)) ->
        exists f, is_choice_function F f.
    End ZFCAxioms.
  End Axioms.

  (** ** Natural Numbers
      
      Von Neumann construction of naturals *)
  Module Naturals.
    Section NaturalNumbers.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      Import Codes.
      Import Axioms.
      
      Axiom successor_code : Alphacarrier -> Alphacarrier.
      Axiom successor_code_spec : forall x,
        is_set_code x -> is_successor x (successor_code x).
      
      (* The first few naturals *)
      Definition zero_zfc := empty_code.
      Definition one_zfc := successor_code zero_zfc.
      Definition two_zfc := successor_code one_zfc.
      Definition three_zfc := successor_code two_zfc.
      
      (* Natural numbers are elements of all inductive sets *)
      Definition is_natural_number (n : Alphacarrier) : Prop :=
        forall I, is_inductive I -> mem n I.
      
      Theorem zero_is_natural : is_natural_number zero_zfc.
      Proof.
        unfold is_natural_number, zero_zfc.
        intros I HI.
        destruct HI as [HIcode [[e [He [Hemp Hemem]]] Hclosed]].
        (* Need axiom that empty sets are unique *)
        Axiom empty_unique : forall e1 e2,
          is_set_code e1 -> is_set_code e2 ->
          (forall x, ~ mem x e1) ->
          (forall x, ~ mem x e2) ->
          e1 = e2.
        assert (e = empty_code).
        { apply empty_unique.
          - exact He.
          - destruct empty_code_spec; assumption.
          - exact Hemp.
          - exact not_mem_empty. }
        subst e.
        exact Hemem.
      Qed.

    End NaturalNumbers.
  End Naturals.

  (** ** Russell and Paradoxes
      
      How paradoxes are handled in our framework *)
  Module Paradoxes.
    Section ParadoxHandling.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      Import Codes.
      Import Axioms.
      
      (* Russell's set *)
      Definition russell_set : ZSet :=
        fun x => is_set_code x /\ ~ mem x x.
      
      (* Russell's set cannot have a code *)
      Theorem russell_has_no_code :
        ~ exists r, is_set_code r /\ set_eq (set_decode r) russell_set.
      Proof.
        intros [r [Hr Hdecode]].
        destruct (alpha_constant_decision (mem r r)) as [Hmem | Hnmem].
        - assert (In r russell_set).
          { apply Hdecode. destruct Hmem as [_ H]. exact H. }
          unfold russell_set, In in H.
          destruct H as [_ Hnot].
          exact (Hnot Hmem).
        - assert (In r russell_set).
          { unfold russell_set, In. split; assumption. }
          assert (mem r r).
          { split; [exact Hr|]. apply Hdecode. exact H. }
          exact (Hnmem H0).
      Qed.
      
      (* Foundation prevents self-membership *)
      Theorem no_set_contains_itself : forall x,
        is_set_code x -> ~ mem x x.
      Proof.
        intros x Hx Hmem.
        destruct (singleton_code_spec x) as [Hs_code Hs_decode].
        assert (exists y, mem y (singleton_code x)).
        { exists x. 
          split.
          - exact Hs_code.
          - apply Hs_decode.
            apply singleton_spec.
            reflexivity. }
        destruct (foundation (singleton_code x) Hs_code H) as [y [Hy Hmin]].
        assert (y = x).
        { destruct Hy as [_ Hy_in].
          apply Hs_decode in Hy_in.
          apply singleton_spec in Hy_in.
          exact Hy_in. }
        subst y.
        apply (Hmin x Hmem).
        split.
        - exact Hs_code.
        - apply Hs_decode. 
          apply singleton_spec. 
          reflexivity.
      Qed.
    End ParadoxHandling.
  End Paradoxes.

  (** ** The Hierarchy
      
      Building mathematics from the void *)
  Module Hierarchy.
    Section CumulativeHierarchy.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      Import Codes.
      Import Axioms.
      Import Operations.
      
      (* Sets have "rank" - distance from the void *)
      Definition rank_0_set (x : Alphacarrier) : Prop :=
        is_set_code x /\ forall y, ~ mem y x.
      
      Definition rank_at_most_n : nat -> Alphacarrier -> Prop :=
        fix rank n x :=
          match n with
          | 0 => rank_0_set x
          | S n' => is_set_code x /\ 
                    forall y, mem y x -> rank n' y
          end.
      
      Theorem empty_rank_0 : rank_at_most_n 0 empty_code.
      Proof.
        unfold rank_at_most_n, rank_0_set.
        destruct empty_code_spec as [Hcode _].
        split.
        - exact Hcode.
        - exact not_mem_empty.
      Qed.
      
      (* The profound insight: Everything comes from nothing *)
      Theorem complement_empty_is_universal :
        set_eq (compl Empty) Universal.
      Proof.
        unfold set_eq, ClassicalAlphaProperties.Predicates.pred_equiv.
        intro x.
        unfold compl, Empty, Universal, In, 
              ClassicalAlphaProperties.Helpers.the_necessary.
        split.
        - intro H. exact H.
        - intro H. exact H.
      Qed.
    End CumulativeHierarchy.
  End Hierarchy.

  Module Theorems.
    Section MainTheorems.
      Context {H_alpha: ClassicalAlphaType}.
      Import Basic.
      Import Fundamental.
      Import Operations.
      Import Algebra.
      Import Codes.
      Import Axioms.
      Import Naturals.
      Import Paradoxes.
      Import Hierarchy.
      
      (** ** Binary Operations via Pairing and Union *)
      
      Theorem binary_union_exists : forall A B,
        is_set_code A -> is_set_code B ->
        exists U, is_set_code U /\ 
          forall x, mem x U <-> (mem x A \/ mem x B).
      Proof.
        intros A B HA HB.
        (* First, create the pair {A, B} *)
        destruct (pair_code_spec A B) as [HP_code HP_decode].
        (* Then take union of this pair *)
        destruct (union_exists (pair_code A B) HP_code) as [U HU].
        exists U.
        destruct HU as [HF_code [HU_code HU_spec]].
        split; [exact HU_code|].
        intro x.
        split.
        - intro HxU.
          apply HU_spec in HxU.
          destruct HxU as [Y [HYP HxY]].
          destruct HYP as [_ HYP_in].
          (* Y is in the pair {A, B} *)
          assert (In Y (pair A B)).
          { apply HP_decode. exact HYP_in. }
          apply pair_spec in H.
          destruct H as [HYA | HYB].
          + left. subst Y. exact HxY.
          + right. subst Y. exact HxY.
        - intros [HxA | HxB].
          + apply HU_spec.
            exists A. split; [|exact HxA].
            split; [exact HP_code|].
            apply HP_decode.
            apply pair_spec. left. reflexivity.
          + apply HU_spec.
            exists B. split; [|exact HxB].
            split; [exact HP_code|].
            apply HP_decode.
            apply pair_spec. right. reflexivity.
      Qed.
      
      Theorem intersection_exists : forall A B,
        is_set_code A -> is_set_code B ->
        exists I, is_set_code I /\
          forall x, mem x I <-> (mem x A /\ mem x B).
      Proof.
        intros A B HA HB.
        apply (separation A (fun x => mem x B) HA).
      Qed.
      
      (** ** Function Images via Replacement *)
      
      Theorem function_image_exists : forall A f,
        is_set_code A ->
        exists B, is_set_code B /\
          forall y, mem y B <-> exists x, mem x A /\ y = f x.
      Proof.
        intros A f HA.
        (* Define the relation R(x,y) := y = f(x) *)
        pose (R := fun x y => y = f x).
        
        (* Show R is functional *)
        assert (Hfunc: is_functional R).
        { unfold is_functional, R.
          intros x y z Hy Hz.
          rewrite Hy. symmetry. exact Hz. }
        
        (* Apply replacement *)
        destruct (replacement A R HA Hfunc) as [B [HB HB_spec]].
        exists B. split; [exact HB|].
        
        intros y. split.
        - intro HyB.
          apply HB_spec in HyB.
          destruct HyB as [x [HxA Hy]].
          exists x. split; [exact HxA|].
          unfold R in Hy. exact Hy.
        - intros [x [HxA Heq]].
          apply HB_spec.
          exists x. split; [exact HxA|].
          unfold R. exact Heq.
      Qed.
      
      (** ** Power Set Properties *)
      
      Theorem empty_in_every_powerset : forall A ps,
        is_set_code A -> is_powerset A ps ->
        mem empty_code ps.
      Proof.
        intros A ps HA Hps.
        destruct Hps as [_ [Hps_code Hps_spec]].
        apply Hps_spec.
        unfold encodes_subset.
        destruct empty_code_spec as [He_code _].
        split; [exact He_code|].
        split; [exact HA|].
        intros y Hy.
        (* y mem empty_code is impossible *)
        exfalso.
        exact (not_mem_empty y Hy).
      Qed.
      
      Theorem set_in_own_powerset : forall A ps,
        is_set_code A -> is_powerset A ps ->
        mem A ps.
      Proof.
        intros A ps HA Hps.
        destruct Hps as [_ [Hps_code Hps_spec]].
        apply Hps_spec.
        unfold encodes_subset.
        split; [exact HA|].
        split; [exact HA|].
        intros y Hy.
        (* y mem A -> y mem A is trivial *)
        exact Hy.
      Qed.
      
      Theorem singleton_in_powerset : forall A ps a,
        is_set_code A -> is_powerset A ps -> mem a A ->
        exists sa, is_set_code sa /\ mem sa ps /\
          forall x, mem x sa <-> x = a.
      Proof.
        intros A ps a HA Hps Ha.
        exists (singleton_code a).
        destruct (singleton_code_spec a) as [Hsa_code Hsa_decode].
        split; [exact Hsa_code|].
        split.
        - (* singleton a is in powerset *)
          destruct Hps as [_ [_ Hps_spec]].
          apply Hps_spec.
          unfold encodes_subset.
          split; [exact Hsa_code|].
          split; [exact HA|].
          intros x Hx.
          destruct Hx as [_ Hx_in].
          assert (In x (singleton a)).
          { apply Hsa_decode. exact Hx_in. }
          assert (x = a).
          { apply singleton_spec. exact H. }
          rewrite H0.
          exact Ha.
        - (* Characterization of singleton *)
          intros x.
          split.
          + intro Hx.
            destruct Hx as [_ Hx_in].
            assert (In x (singleton a)).
            { apply Hsa_decode. exact Hx_in. }
            apply singleton_spec.
            exact H.
          + intro Heq.
            rewrite Heq.
            split; [exact Hsa_code|].
            apply Hsa_decode.
            apply singleton_spec.
            reflexivity.
      Qed.
      
      (** ** Natural Number Induction *)
      
      (* First we need these axioms *)
      Axiom nat_set_code : Alphacarrier.
      Axiom nat_set_code_spec : 
        is_set_code nat_set_code /\
        forall n, mem n nat_set_code <-> is_natural_number n.
      
      Axiom nat_is_set_code : forall n,
        is_natural_number n -> is_set_code n.
      
      Axiom successor_preserves_nat : forall n,
        is_natural_number n -> is_natural_number (successor_code n).
      
      Theorem nat_induction : forall (P : Alphacarrier -> Prop),
        P zero_zfc ->
        (forall n, is_natural_number n -> P n -> P (successor_code n)) ->
        forall n, is_natural_number n -> P n.
      Proof.
        intros P Hz Hsucc n Hn.
        
        (* The subset of naturals satisfying P *)
        destruct nat_set_code_spec as [Hnat_code Hnat_spec].
        destruct (separation nat_set_code P Hnat_code) as [S [HS HS_spec]].
        
        (* Claim: S is inductive *)
        assert (His_ind: is_inductive S).
        { unfold is_inductive.
          split; [exact HS|].
          split.
          - (* S contains zero *)
            exists zero_zfc.
            split; [|split].
            + destruct empty_code_spec; assumption.
            + exact not_mem_empty.
            + apply HS_spec. split.
              * apply Hnat_spec. exact zero_is_natural.
              * exact Hz.
          - (* S is closed under successor *)
            intros x HxS.
            assert (Hx_components: mem x nat_set_code /\ P x).
            { apply HS_spec. exact HxS. }
            destruct Hx_components as [Hx_in_nat Px].
            
            assert (Hx_nat: is_natural_number x).
            { apply Hnat_spec. exact Hx_in_nat. }
            
            assert (Hx_code: is_set_code x).
            { apply nat_is_set_code. exact Hx_nat. }
            
            exists (successor_code x).
            split.
            + apply successor_code_spec. exact Hx_code.
            + apply HS_spec. split.
              * apply Hnat_spec. 
                apply successor_preserves_nat. exact Hx_nat.
              * apply Hsucc; assumption. }
        
        (* Since n is natural, it's in S *)
        assert (n_in_S: mem n S).
        { unfold is_natural_number in Hn.
          exact (Hn S His_ind). }
        
        (* Therefore P n holds *)
        apply HS_spec in n_in_S.
        destruct n_in_S as [_ Pn].
        exact Pn.
      Qed.
      
      (** ** Cantor's Theorem - The Crown Jewel *)
      
      (* Helper for converting between different membership notions *)
      Lemma mem_iff_is_member : forall a b,
        mem a b <-> is_set_code b /\ In a (set_decode b).
      Proof.
        intros a b.
        split; intro H; exact H.
      Qed.
      
      Theorem cantor_theorem : forall A ps,
        is_set_code A -> is_powerset A ps ->
        ~ exists f : Alphacarrier -> Alphacarrier,
          (forall x, mem x A -> mem (f x) ps) /\
          (forall y, mem y ps -> exists x, mem x A /\ y = f x).
      Proof.
        intros A ps HA Hps [f [Hf_maps Hf_onto]].
        
        (* Define the diagonal set D = {x ∈ A | x ∉ f(x)} *)
        destruct (separation A (fun x => ~ mem x (f x)) HA) as [D [HD HD_spec]].
        
        (* D is a subset of A, so D ∈ P(A) *)
        assert (HD_in_ps: mem D ps).
        { destruct Hps as [_ [_ Hps_spec]].
          apply Hps_spec.
          unfold encodes_subset.
          split; [exact HD|].
          split; [exact HA|].
          intros y Hy.
          apply HD_spec in Hy.
          destruct Hy as [H_mem_A _].
          exact H_mem_A. }
        
        (* Since f is onto, D = f(d) for some d ∈ A *)
        destruct (Hf_onto D HD_in_ps) as [d [Hd Heq]].
        
        (* Now the contradiction: d ∈ D ↔ d ∉ f(d) = D *)
        destruct (alpha_constant_decision (mem d D)) as [Hd_in | Hd_out].
        - (* d ∈ D, so d ∉ f(d) = D, contradiction *)
          assert (H_contra : mem d A /\ ~ mem d (f d)).
          { apply HD_spec. exact Hd_in. }
          destruct H_contra as [_ Hnot_fd].
          rewrite Heq in Hd_in.
          exact (Hnot_fd Hd_in).
        - (* d ∉ D, so by definition of D, d ∈ f(d) = D *)
          assert (mem d D).
          { apply HD_spec.
            split.
            + exact Hd.
            + rewrite <- Heq. exact Hd_out. }
          exact (Hd_out H).
      Qed.
      
      (** ** Rank and Hierarchy Properties *)
      
      Theorem singleton_rank_1 : forall a,
        rank_at_most_n 0 a ->
        rank_at_most_n 1 (singleton_code a).
      Proof.
        intros a H0.
        simpl.
        destruct (singleton_code_spec a) as [Hcode Hdecode].
        split; [exact Hcode|].
        intros y Hy.
        (* mem y (singleton_code a) means y = a *)
        destruct Hy as [_ Hy_in].
        assert (In y (singleton a)) by (apply Hdecode; exact Hy_in).
        assert (y = a) by (apply singleton_spec; exact H).
        subst y.
        exact H0.
      Qed.
    End MainTheorems.
  End Theorems.
End ZFC.


(** * ZFC Metatheory *)

Module ZFCMeta.
  Section Metatheory.
    Context {H_alpha: ClassicalAlphaType}.
    Import ZFC.Basic.
    Import ZFC.Fundamental.
    Import ZFC.Operations.
    Import ZFC.Codes.
    Import ZFC.Axioms.
    
    (** ** Uniqueness Results *)
    
    (* Key axiom: codes are extensional *)
    Axiom code_extensionality : forall c1 c2,
      is_set_code c1 -> is_set_code c2 ->
      set_eq (set_decode c1) (set_decode c2) ->
      c1 = c2.
    
    (* Empty sets are unique *)
    Theorem empty_unique : forall e1 e2,
      is_set_code e1 -> is_set_code e2 ->
      (forall x, ~ mem x e1) ->
      (forall x, ~ mem x e2) ->
      e1 = e2.
    Proof.
      intros e1 e2 He1 He2 Hemp1 Hemp2.
      apply code_extensionality; try assumption.
      unfold set_eq, ClassicalAlphaProperties.Predicates.pred_equiv.
      intro x.
      split; intro Hx; exfalso.
      - apply (Hemp1 x). split; [exact He1 | exact Hx].
      - apply (Hemp2 x). split; [exact He2 | exact Hx].
    Qed.
    
    (* Powersets are unique *)
    Theorem powerset_unique : forall A ps1 ps2,
      is_powerset A ps1 -> is_powerset A ps2 ->
      ps1 = ps2.
    Proof.
      intros A ps1 ps2 Hps1 Hps2.
      destruct Hps1 as [HA1 [Hps1_code Hps1_spec]].
      destruct Hps2 as [HA2 [Hps2_code Hps2_spec]].
      apply code_extensionality; try assumption.
      unfold set_eq, ClassicalAlphaProperties.Predicates.pred_equiv.
      intro x.
      split; intro Hx.
      - assert (mem x ps1) by (split; [exact Hps1_code | exact Hx]).
        apply Hps1_spec in H.
        apply Hps2_spec in H.
        destruct H as [_ Hx2].
        exact Hx2.
      - assert (mem x ps2) by (split; [exact Hps2_code | exact Hx]).
        apply Hps2_spec in H.
        apply Hps1_spec in H.
        destruct H as [_ Hx1].
        exact Hx1.
    Qed.
    
    (** ** Choice-free Powerset Selection *)
    
    (* Since powersets are unique, we can axiomatize a selection function *)
    Axiom powerset_selector : Alphacarrier -> Alphacarrier.
    Axiom powerset_selector_spec : forall A,
      is_set_code A -> is_powerset A (powerset_selector A).
    
    (* Every non-empty set contains a member *)
    Lemma non_empty_has_member : forall x,
      is_set_code x ->
      x <> empty_code ->
      exists y, mem y x.
    Proof.
      intros x Hx Hne.
      apply ClassicalAlphaProperties.Existence.not_all_not_ex.
      intro Hall_not.
      apply Hne.
      apply code_extensionality; try assumption.
      - destruct empty_code_spec; assumption.
      - unfold set_eq, ClassicalAlphaProperties.Predicates.pred_equiv.
        intro z.
        split; intro Hz.
        + (* z ∈ set_decode x → z ∈ set_decode empty_code *)
          exfalso.
          apply (Hall_not z).
          split; [exact Hx | exact Hz].
        + (* z ∈ set_decode empty_code → z ∈ set_decode x *)
          destruct empty_code_spec as [_ Hempty_decode].
          apply Hempty_decode in Hz.
          unfold In, Empty in Hz.
          exfalso.
          exact (ClassicalAlphaProperties.Core.classical_veil_is_impossible z Hz).
    Qed.
    
  End Metatheory.
End ZFCMeta.

(* Show there's always a path back to empty set (omega_veil in our framework)*)
Module ZFCVoid.
  Section VoidGeneratesAll.
    Context {H_alpha: ClassicalAlphaType}.
    Import ZFC.Basic ZFC.Fundamental ZFC.Operations ZFC.Codes.
    Import ZFCMeta.
    
    (* ========== The Clean Mathematical Statement ========== *)
    Axiom mem_well_founded : forall P : Alphacarrier -> Prop,
    (forall x, is_set_code x -> 
      (forall y, mem y x -> P y) -> P x) ->
    forall x, is_set_code x -> P x.
    
    Theorem void_generates_all : forall x,
      is_set_code x ->
      x = empty_code \/ 
      exists (depth : nat) (path : nat -> Alphacarrier),
        depth > 0 /\
        path 0 = empty_code /\
        path depth = x /\
        (forall i, i < depth -> mem (path i) (path (S i))).
    Proof.
      intros x Hx.
      revert Hx.
      apply (mem_well_founded (fun x => 
        x = empty_code \/ 
        exists depth path,
          depth > 0 /\
          path 0 = empty_code /\
          path depth = x /\
          forall i, i < depth -> mem (path i) (path (S i)))).
      
      intros y Hy IH.
      destruct (alpha_constant_decision (y = empty_code)) as [Heq | Hne].
      - (* y is empty *)
        left. exact Heq.
        
      - (* y is non-empty, so it contains something *)
        right.
        destruct (non_empty_has_member y Hy Hne) as [z Hz_mem].
        (* Hz_mem : mem z y *)
        destruct (IH z Hz_mem) as [Hz_empty | Hz_chain].
        
        + (* Case 1: z is empty, so the chain is [empty; y] *)
          exists 1.
          exists (fun i => match i with
                          | 0 => empty_code
                          | _ => y
                          end).
          split; [lia|].
          split; [reflexivity|].
          split; [reflexivity|].
          intros i Hi.
          assert (i = 0) by lia.
          subst i.
          simpl.
          rewrite <- Hz_empty.
          exact Hz_mem.  (* Now this has the right type: mem z y *)
        
        + (* Case 2: z has a chain, extend it with y *)
          destruct Hz_chain as [n [path_z [Hn [Hz_start [Hz_end Hz_links]]]]].
          exists (S n).
          exists (fun i => if Nat.eq_dec i (S n) then y else path_z i).
          split; [lia|].
          split.
          * (* Still starts with empty *)
            destruct (Nat.eq_dec 0 (S n)); [lia | exact Hz_start].
          * split.
            -- (* Now ends with y *)
              destruct (Nat.eq_dec (S n) (S n)); [reflexivity | contradiction].
            -- (* Links are preserved and one new link added *)
              intros i Hi.
              destruct (lt_eq_lt_dec i n) as [[Hi_lt | Hi_eq] | Hi_gt].
              ++ (* i < n: old links preserved *)
                  destruct (Nat.eq_dec i (S n)) as [Heq | Hneq]; [lia|].
                  destruct (Nat.eq_dec (S i) (S n)) as [Heq' | Hneq'].
                  ** (* S i = S n impossible since i < n *)
                    lia.
                  ** (* Both use path_z *)
                    apply Hz_links. exact Hi_lt.
                ++ (* i = n: the new link from z to y *)
                  subst i.
                  destruct (Nat.eq_dec n (S n)) as [Heq | Hneq]; [lia|].
                  destruct (Nat.eq_dec (S n) (S n)) as [Heq' | Hneq']; 
                    [|contradiction].
                  (* We need: mem (path_z n) y *)
                  (* We have: path_z n = z and mem z y *)
                  assert (path_z n = z) by exact Hz_end.
                  rewrite H.
                  exact Hz_mem.
              ++ (* i > n impossible since i < S n *)
                  lia.
    Qed.
    
    (* ========== Corollaries ========== *)
    
    Corollary every_set_has_rank : forall x,
      is_set_code x ->
      exists n : nat, 
        (n = 0 /\ x = empty_code) \/
        (n > 0 /\ exists path : nat -> Alphacarrier,
          path 0 = empty_code /\
          path n = x /\
          forall i, i < n -> mem (path i) (path (S i))).
    Proof.
      intros x Hx.
      destruct (void_generates_all x Hx) as [Heq | [n [path [Hn H]]]].
      - exists 0. left. split; [reflexivity | exact Heq].
      - exists n. right. split; [exact Hn | exists path; exact H].
    Qed.
    
    Definition has_membership_depth (x : Alphacarrier) (n : nat) : Prop :=
    is_set_code x /\
    ((n = 0 /\ x = empty_code) \/
    (n > 0 /\ exists path : nat -> Alphacarrier,
      path 0 = empty_code /\
      path n = x /\
      forall i, i < n -> mem (path i) (path (S i)))).

    Theorem every_set_has_depth : forall x,
      is_set_code x -> exists n, has_membership_depth x n.
    Proof.
      intros x Hx.
      destruct (void_generates_all x Hx) as [Heq | [n [path [Hn [H0 [Hend Hlinks]]]]]].
      - exists 0. split; [exact Hx|]. left. split; [reflexivity|exact Heq].
      - exists n. split; [exact Hx|]. right. 
        split; [exact Hn|].
        exists path. auto.
    Qed.
    
    (* First we need this axiom - it's reasonable in ZFC *)
    Axiom mem_implies_set_code : forall a b,
      is_set_code b -> mem a b -> is_set_code a.

    Theorem void_is_foundation : 
      (forall x, is_set_code x -> 
        x = empty_code \/ exists y, is_set_code y /\ mem y x) /\
      (exists x, is_set_code x /\ x = empty_code) /\
      (forall x, is_set_code x -> exists n : nat,
        n = 0 /\ x = empty_code \/
        n > 0 /\ exists y, is_set_code y /\ mem y x).
    Proof.
      split; [|split].
      - (* Every set is either empty or contains something *)
        intros x Hx.
        destruct (alpha_constant_decision (x = empty_code)) as [Heq | Hne].
        + left. exact Heq.
        + right. 
          destruct (non_empty_has_member x Hx Hne) as [y Hy_mem].
          exists y.
          split.
          * apply (mem_implies_set_code y x); assumption.
          * exact Hy_mem.
        
      - (* The empty set exists *)
        exists empty_code.
        destruct empty_code_spec as [Hcode _].
        split; [exact Hcode | reflexivity].
        
      - (* Every set either is empty or contains something, with rank *)
        intros x Hx.
        destruct (alpha_constant_decision (x = empty_code)) as [Heq | Hne].
        + (* x is empty *)
          exists 0. left. split; [reflexivity | exact Heq].
        + (* x is non-empty *)
          destruct (non_empty_has_member x Hx Hne) as [y Hy_mem].
          exists 1. right.
          split; [lia|].
          exists y.
          split.
          * apply (mem_implies_set_code y x); assumption.
          * exact Hy_mem.
    Qed.
    
  End VoidGeneratesAll.
End ZFCVoid.