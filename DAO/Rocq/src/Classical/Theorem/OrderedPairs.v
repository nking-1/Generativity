(** * OrderedPairs.v - Ordered Pairs & Relations in ZFC *)

Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.
Require Import DAO.Classical.Theory.ZFC.
Require Import Corelib.Classes.RelationClasses.

Module OrderedPairs.
  Import ZFC.Basic ZFC.Fundamental ZFC.Operations ZFC.Codes ZFC.Axioms.
  Import ZFCMeta.
  
  Section OrderedPairDefinition.
    Context {H_alpha: ClassicalAlphaType}.
    
    (** Kuratowski's definition at the predicate level *)
    Definition ordered_pair_pred (a b : Alphacarrier) : ZSet :=
      fun x => In x (singleton a) \/ In x (pair a b).
    
    Definition ordered_pair_code (a b : Alphacarrier) : Alphacarrier :=
      pair_code (singleton_code a) (pair_code a b).
    
    Theorem ordered_pair_code_spec : forall a b,
      is_set_code a -> is_set_code b ->
      is_set_code (ordered_pair_code a b) /\
      forall x, is_set_code x -> 
        (mem x (ordered_pair_code a b) <-> 
         (set_eq (set_decode x) (singleton a) \/ 
          set_eq (set_decode x) (pair a b))).
    Proof.
      intros a b Ha Hb.
      unfold ordered_pair_code.
      destruct (singleton_code_spec a) as [Hs1 Hs1_eq].
      destruct (pair_code_spec a b) as [Hp2 Hp2_eq].
      destruct (pair_code_spec (singleton_code a) (pair_code a b)) as [Hpair Hpair_eq].
      split; [exact Hpair|].
      
      intros x Hx.
      split.
      - intro Hmem.
        destruct Hmem as [_ Hin].
        apply Hpair_eq in Hin.
        apply pair_spec in Hin.
        destruct Hin as [Heq1 | Heq2].
        + left. 
          subst x.
          exact Hs1_eq.
        + right.
          subst x.
          exact Hp2_eq.
      - intros [Heq1 | Heq2].
        + split; [exact Hpair|].
          apply Hpair_eq.
          apply pair_spec.
          left.
          assert (x = singleton_code a).
          { apply code_extensionality; auto.
            unfold set_eq in *.
            intro z.
            split.
            - intro Hz. apply Hs1_eq. apply Heq1. exact Hz.
            - intro Hz. apply Heq1. apply Hs1_eq. exact Hz. }
          exact H.
        + split; [exact Hpair|].
          apply Hpair_eq.
          apply pair_spec.
          right.
          assert (x = pair_code a b).
          { apply code_extensionality; auto.
            unfold set_eq in *.
            intro z.
            split.
            - intro Hz. apply Hp2_eq. apply Heq2. exact Hz.
            - intro Hz. apply Heq2. apply Hp2_eq. exact Hz. }
          exact H.
    Qed.
    
    Theorem ordered_pair_not_empty : forall a b : Alphacarrier,
      is_set_code a -> is_set_code b ->
      ordered_pair_code a b <> empty_code.
    Proof.
      intros a b Ha Hb Heq.
      destruct (ordered_pair_code_spec a b Ha Hb) as [Hcode Hspec].
      
      (* Get the properties of singleton_code a *)
      destruct (singleton_code_spec a) as [Hs_code Hs_eq].
      
      (* singleton_code a is a member *)
      assert (mem (singleton_code a) (ordered_pair_code a b)).
      { split; [exact Hcode|].
        apply Hspec; [exact Hs_code|].
        left. exact Hs_eq. }
      
      rewrite Heq in H.
      exact (not_mem_empty _ H).
    Qed.
    
  End OrderedPairDefinition.
  
  Section Relations.
    Context {H_alpha: ClassicalAlphaType}.
    
    (** Check if something is an ordered pair *)
    Definition is_ordered_pair (p : Alphacarrier) : Prop :=
      is_set_code p /\
      exists a b : Alphacarrier, 
        is_set_code a /\ is_set_code b /\
        p = ordered_pair_code a b.
    
    (** A relation is a set of ordered pairs *)
    Definition is_relation (R : Alphacarrier) : Prop :=
      is_set_code R /\
      forall z, mem z R -> is_ordered_pair z.
    
    (* Axiomatize computational versions of union and separation *)
    Axiom union_code : Alphacarrier -> Alphacarrier.
    Axiom union_code_spec : forall F,
      is_set_code F ->
      is_union_of F (union_code F).
    
    Axiom separation_code : Alphacarrier -> (Alphacarrier -> Prop) -> Alphacarrier.
    Axiom separation_code_spec : forall A P,
      is_set_code A ->
      is_set_code (separation_code A P) /\
      forall x, mem x (separation_code A P) <-> (mem x A /\ P x).
    
    (* Helper lemma *)
    Lemma union_code_is_set : forall F,
      is_set_code F -> is_set_code (union_code F).
    Proof.
      intros F HF.
      destruct (union_code_spec F HF) as [_ [HU _]].
      exact HU.
    Qed.
    
    (** Now we can define domain *)
    Definition dom_code (R : Alphacarrier) : Alphacarrier :=
      separation_code 
        (union_code (union_code R))
        (fun x => exists y, is_set_code y /\ mem (ordered_pair_code x y) R).
    
    Theorem dom_code_spec : forall R,
      is_set_code R ->
      is_relation R ->
      is_set_code (dom_code R) /\
      forall x, is_set_code x ->
        (mem x (dom_code R) <-> 
        exists y, is_set_code y /\ mem (ordered_pair_code x y) R).
    Proof.
      intros R HR HRel.
      unfold dom_code.
      assert (HU1: is_set_code (union_code R)) by (apply union_code_is_set; auto).
      assert (HU2: is_set_code (union_code (union_code R))) by (apply union_code_is_set; auto).
      
      destruct (separation_code_spec 
               (union_code (union_code R)) 
               (fun x => exists y, is_set_code y /\ mem (ordered_pair_code x y) R)
               HU2) as [HD Hspec].
      split; [exact HD|].
      
      intros x Hx.
      split.
      - intro Hmem.
        apply Hspec in Hmem.
        destruct Hmem as [_ Hex].
        exact Hex.
      - intros [y [Hy Hmem]].
        apply Hspec.
        split; [|exists y; split; assumption].
        
        (* Show x ∈ ⋃⋃R *)
        destruct (union_code_spec R HR) as [_ [_ HU1spec]].
        destruct (union_code_spec (union_code R) HU1) as [_ [_ HU2spec]].
        
        apply HU2spec.
        (* Need to show: ∃Y. mem Y (union_code R) ∧ mem x Y *)
        exists (singleton_code x).
        split.
        + (* Show singleton_code x ∈ ⋃R *)
          apply HU1spec.
          (* ∃Z. mem Z R ∧ mem (singleton_code x) Z *)
          exists (ordered_pair_code x y).
          split; [exact Hmem|].
          (* Show singleton_code x ∈ ordered_pair_code x y *)
          destruct (ordered_pair_code_spec x y Hx Hy) as [Hpair_code Hpair_spec].
          destruct (singleton_code_spec x) as [Hs_code Hs_eq].
          split.
          * exact Hpair_code.  (* ordered_pair_code x y is a set code *)
          * apply Hpair_spec; [exact Hs_code|left; exact Hs_eq].
        + (* Show x ∈ singleton_code x *)
          destruct (singleton_code_spec x) as [Hs_code' Hs_eq'].
          split; [exact Hs_code'|].
          apply Hs_eq'.
          apply singleton_spec.
          reflexivity.
    Qed.
  End Relations.

  Section OrderedPairEquality.
    Context {H_alpha: ClassicalAlphaType}.
    
    (** Key lemma: A singleton can only equal a pair if the pair has both elements the same *)
    Lemma singleton_eq_pair : forall a b c,
      is_set_code a -> is_set_code b -> is_set_code c ->
      set_eq (set_decode (singleton_code a)) (set_decode (pair_code b c)) ->
      a = b /\ b = c.
    Proof.
      intros a b c Ha Hb Hc Heq.
      destruct (singleton_code_spec a) as [_ Hsa].
      destruct (pair_code_spec b c) as [_ Hpair].
      
      (* The singleton {a} has exactly one element: a *)
      (* The pair {b,c} has one or two elements: b and possibly c *)
      
      (* First show a ∈ {b,c} *)
      assert (In a (pair b c)).
      { apply Hpair. apply Heq. apply Hsa. apply singleton_spec. reflexivity. }
      apply pair_spec in H.
      destruct H as [Hab | Hac].
      
      - (* Case: a = b *)
        subst b.
        split; [reflexivity|].
        
        (* Now show c = a by showing c ∈ {a} *)
        assert (In c (singleton a)).
        { apply Hsa. apply Heq. apply Hpair. apply pair_spec. right. reflexivity. }
        apply singleton_spec in H.
        symmetry. exact H.
        
      - (* Case: a = c *)
        (* Show b ∈ {a} *)
        assert (In b (singleton a)).
        { apply Hsa. apply Heq. apply Hpair. apply pair_spec. left. reflexivity. }
        apply singleton_spec in H.
        
        (* Now we have H : b = a and Hac : a = c *)
        split.
        + (* a = b *) symmetry. exact H.
        + (* b = c *) rewrite H. exact Hac.
    Qed.
    
    (** Lemma: Pairs have at most 2 elements *)
    Lemma pair_cardinality : forall a b c,
      is_set_code a -> is_set_code b -> is_set_code c ->
      mem c (pair_code a b) ->
      c = a \/ c = b.
    Proof.
      intros a b c Ha Hb Hc Hmem.
      destruct (pair_code_spec a b) as [_ Hspec].
      destruct Hmem as [_ Hin].
      apply Hspec in Hin.
      apply pair_spec in Hin.
      exact Hin.
    Qed.

    (** Helper: If two pairs of codes are equal as sets, their elements match up *)
    (** Helper: If two pairs of codes are equal as sets, their elements match up *)
    Lemma pair_code_elements : forall x y z w,
      is_set_code x -> is_set_code y -> is_set_code z -> is_set_code w ->
      set_eq (set_decode (pair_code x y)) (set_decode (pair_code z w)) ->
      (x = z /\ y = w) \/ (x = w /\ y = z).
    Proof.
      intros x y z w Hx Hy Hz Hw Heq.
      
      (* First, establish that codes with equal decodes are equal *)
      assert (pair_code x y = pair_code z w).
      { apply code_extensionality.
        - apply (proj1 (pair_code_spec x y)).
        - apply (proj1 (pair_code_spec z w)).
        - exact Heq. }
      
      (* Get the decode specifications *)
      destruct (pair_code_spec x y) as [_ Hxy_spec].
      destruct (pair_code_spec z w) as [_ Hzw_spec].
      
      (* x ∈ {x,y} *)
      assert (Hx_in: In x (pair x y)) by (apply pair_spec; left; reflexivity).
      
      (* So x ∈ {z,w} by the equality *)
      assert (Hx_in_zw: In x (pair z w)).
      { apply Hzw_spec. apply Heq. apply Hxy_spec. exact Hx_in. }
      
      apply pair_spec in Hx_in_zw.
      destruct Hx_in_zw as [Hxz | Hxw].
      
      - (* Case: x = z *)
        left. split; [exact Hxz|].
        
        (* Need to show y = w *)
        (* y ∈ {x,y} *)
        assert (Hy_in: In y (pair x y)) by (apply pair_spec; right; reflexivity).
        
        (* So y ∈ {z,w} *)
        assert (Hy_in_zw: In y (pair z w)).
        { apply Hzw_spec. apply Heq. apply Hxy_spec. exact Hy_in. }
        
        apply pair_spec in Hy_in_zw.
        destruct Hy_in_zw as [Hyz | Hyw].
        + (* y = z *)
          (* We have x = z and y = z, so x = y *)
          subst z.
          (* Now we need to show y = w *)
          (* Since {x,y} = {x,w} and we know w ∈ {x,w} *)
          assert (Hw_in: In w (pair x y)).
          { apply Hxy_spec. 
            unfold set_eq in Heq.
            apply (proj2 (Heq w)).  (* Apply Heq backwards *)
            apply Hzw_spec. 
            apply pair_spec. right. reflexivity. }
          
          apply pair_spec in Hw_in.
          destruct Hw_in; auto.
          (* If w = x and x = y, then w = y *)
          subst. reflexivity.
          
        + (* y = w *)
          exact Hyw.
      
      - (* Case: x = w *)
        right. split; [exact Hxw|].
        
        (* Need to show y = z *)
        assert (Hy_in: In y (pair x y)) by (apply pair_spec; right; reflexivity).
        assert (Hy_in_zw: In y (pair z w)).
        { apply Hzw_spec. apply Heq. apply Hxy_spec. exact Hy_in. }
        
        apply pair_spec in Hy_in_zw.
        destruct Hy_in_zw as [Hyz | Hyw].
        + (* y = z *)
          exact Hyz.
        + (* y = w *)
          (* We have x = w and y = w, so x = y *)
          subst w.
          (* Since {x,y} = {z,x} and we know z ∈ {z,x} *)
          assert (Hz_in: In z (pair x y)).
          { apply Hxy_spec. 
            unfold set_eq in Heq.
            apply (proj2 (Heq z)).  (* Apply Heq backwards *)
            apply Hzw_spec. 
            apply pair_spec. left. reflexivity. }
          
          apply pair_spec in Hz_in.
          destruct Hz_in; auto.
          subst. reflexivity.
    Qed.

      Section DegenerateCases.
        (** When a pair has repeated elements, it equals a singleton *)
        Lemma pair_repeated_eq_singleton : forall a,
          is_set_code a ->
          set_eq (set_decode (pair_code a a)) (set_decode (singleton_code a)).
        Proof.
          intros a Ha.
          destruct (pair_code_spec a a) as [_ Hpair].
          destruct (singleton_code_spec a) as [_ Hsing].
          unfold set_eq. intro x.
          split; intro H.
          - (* set_decode (pair_code a a) x → set_decode (singleton_code a) x *)
            apply Hsing. 
            apply singleton_spec.
            apply Hpair in H.
            apply pair_spec in H.
            destruct H; assumption.
          - (* set_decode (singleton_code a) x → set_decode (pair_code a a) x *)
            apply Hpair.
            apply pair_spec.
            apply Hsing in H.
            assert (x = a).
            { apply singleton_spec. exact H. }
            subst. left. reflexivity.
        Qed.
        
        (** Singleton can only equal pair if pair has repeated elements *)
        Lemma singleton_eq_pair_implies_repeated : forall a b c,
          is_set_code a -> is_set_code b -> is_set_code c ->
          set_eq (set_decode (singleton_code a)) (set_decode (pair_code b c)) ->
          a = b /\ b = c.
        Proof.
          (* Already proved above as singleton_eq_pair *)
          apply singleton_eq_pair.
        Qed.
        
        (** If singleton_code equals pair_code, extract the elements *)
        Lemma singleton_code_eq_pair_code : forall a b c,
          is_set_code a -> is_set_code b -> is_set_code c ->
          singleton_code a = pair_code b c ->
          a = b /\ b = c.
        Proof.
          intros a b c Ha Hb Hc Heq.
          apply singleton_eq_pair; auto.
          (* We need to show: set_eq (set_decode (singleton_code a)) (set_decode (pair_code b c)) *)
          (* Since singleton_code a = pair_code b c, their decodes are equal *)
          unfold set_eq. intro x.
          split; intro H.
          - (* set_decode (singleton_code a) x → set_decode (pair_code b c) x *)
            rewrite <- Heq. exact H.
          - (* set_decode (pair_code b c) x → set_decode (singleton_code a) x *)  
            rewrite Heq. exact H.
        Qed.
        
        (** If pair_code equals singleton_code, extract the constraint *)
        Lemma pair_code_eq_singleton_code : forall a b c,
          is_set_code a -> is_set_code b -> is_set_code c ->
          pair_code a b = singleton_code c ->
          a = c /\ b = c.
        Proof.
          intros a b c Ha Hb Hc Heq.
          symmetry in Heq.
          apply singleton_code_eq_pair_code in Heq; auto.
          destruct Heq as [Hca Hac].
          split; auto.
          (* b = c *)
          transitivity a; auto.
        Qed.
        
        (** Key lemma: ordered pair with repeated first element *)
        Lemma ordered_pair_repeated_first : forall a b,
          is_set_code a -> is_set_code b ->
          a = b ->
          set_eq (set_decode (ordered_pair_code a b)) 
                (set_decode (singleton_code (singleton_code a))).
        Proof.
          intros a b Ha Hb Heq.
          subst b.
          unfold ordered_pair_code.
          (* (a,a) = {{a},{a,a}} = {{a},{a}} = {{a}} *)
          assert (H1: set_eq (set_decode (pair_code a a)) (set_decode (singleton_code a))).
          { apply pair_repeated_eq_singleton; auto. }
          
          (* So pair_code (singleton_code a) (pair_code a a) = 
                pair_code (singleton_code a) (singleton_code a) *)
          assert (H2: pair_code a a = singleton_code a).
          { apply code_extensionality.
            - apply (proj1 (pair_code_spec a a)).
            - apply (proj1 (singleton_code_spec a)).
            - exact H1. }
          
          rewrite H2.
          apply pair_repeated_eq_singleton.
          apply (proj1 (singleton_code_spec a)).
        Qed.

        (** Injectivity of singleton_code *)
        Lemma singleton_code_injective : forall a b,
          is_set_code a -> is_set_code b ->
          singleton_code a = singleton_code b ->
          a = b.
        Proof.
          intros a b Ha Hb Heq.
          (* From singleton_code equality, we get set equality *)
          assert (set_eq (set_decode (singleton_code a)) (set_decode (singleton_code b))).
          { unfold set_eq. intro x. rewrite Heq. reflexivity. }
          
          (* Which means {a} = {b} as sets *)
          destruct (singleton_code_spec a) as [_ Hsa].
          destruct (singleton_code_spec b) as [_ Hsb].
          assert (set_eq (singleton a) (singleton b)).
          { unfold set_eq in *. intro x.
            split; intro Hx.
            - (* singleton a x → singleton b x *)
              apply Hsb. apply H. apply Hsa. exact Hx.
            - (* singleton b x → singleton a x *)
              apply Hsa. apply H. apply Hsb. exact Hx. }
          
          (* If {a} = {b}, then a ∈ {b}, so a = b *)
          assert (In a (singleton b)).
          { apply H0. apply singleton_spec. reflexivity. }
          apply singleton_spec in H1.
          exact H1.
        Qed.
        
        (** When both ordered pairs are degenerate *)
        Lemma both_degenerate_case : forall a b c d,
          is_set_code a -> is_set_code b -> is_set_code c -> is_set_code d ->
          a = b -> c = d ->
          ordered_pair_code a b = ordered_pair_code c d ->
          a = c.
        Proof.
          intros a b c d Ha Hb Hc Hd Hab Hcd Heq.
          subst b d.
          (* Both become {{a}} and {{c}} *)
          assert (H1: set_eq (set_decode (ordered_pair_code a a)) 
                            (set_decode (singleton_code (singleton_code a)))).
          { apply ordered_pair_repeated_first; auto. }
          
          assert (H2: set_eq (set_decode (ordered_pair_code c c)) 
                            (set_decode (singleton_code (singleton_code c)))).
          { apply ordered_pair_repeated_first; auto. }
          
          (* From Heq: singleton_code (singleton_code a) = singleton_code (singleton_code c) *)
          assert (H3: singleton_code (singleton_code a) = singleton_code (singleton_code c)).
          { apply code_extensionality.
            - apply (proj1 (singleton_code_spec (singleton_code a))).
            - apply (proj1 (singleton_code_spec (singleton_code c))).
            - unfold set_eq in *. intro x.
              split; intro Hx.
              + (* left to right *)
                apply H2. rewrite <- Heq. apply H1. exact Hx.
              + (* right to left *)
                apply H1. rewrite Heq. apply H2. exact Hx. }
          
          (* Apply singleton injectivity twice *)
          apply singleton_code_injective in H3; auto.
          apply singleton_code_injective in H3; auto.
          - apply (proj1 (singleton_code_spec a)).
          - apply (proj1 (singleton_code_spec c)).
        Qed.
        
      End DegenerateCases.
    
    (** Key lemma for ordered pair equality *)
    Lemma pair_eq_cases : forall a b c d,
      is_set_code a -> is_set_code b -> is_set_code c -> is_set_code d ->
      set_eq (set_decode (pair_code (singleton_code a) (pair_code a b)))
             (set_decode (pair_code (singleton_code c) (pair_code c d))) ->
      ((singleton_code a = singleton_code c /\ pair_code a b = pair_code c d) \/
       (singleton_code a = pair_code c d /\ pair_code a b = singleton_code c)).
    Proof.
      intros a b c d Ha Hb Hc Hd Heq.
      
      (* Get the singleton and pair codes *)
      destruct (singleton_code_spec a) as [Hsa_code _].
      destruct (singleton_code_spec c) as [Hsc_code _].
      destruct (pair_code_spec a b) as [Hab_code _].
      destruct (pair_code_spec c d) as [Hcd_code _].
      
      (* Apply pair_code_elements to the outer pairs *)
      apply pair_code_elements in Heq; auto.
    Qed.
    
    (** Now we can prove the fundamental theorem *)
    Theorem ordered_pair_equality_proof : forall a b c d : Alphacarrier,
      is_set_code a -> is_set_code b -> is_set_code c -> is_set_code d ->
      ordered_pair_code a b = ordered_pair_code c d ->
      a = c /\ b = d.
    Proof.
      intros a b c d Ha Hb Hc Hd Heq.
      
      (* Apply extensionality to get set equality *)
      assert (Hset_eq: set_eq (set_decode (ordered_pair_code a b)) 
                              (set_decode (ordered_pair_code c d))).
      { unfold set_eq. intro x. split; intro H.
        - rewrite <- Heq. exact H.
        - rewrite Heq. exact H. }
      
      (* Unfold the definition *)
      unfold ordered_pair_code in *.
      
      (* Apply the cases lemma *)
      destruct (pair_eq_cases a b c d Ha Hb Hc Hd Hset_eq) as [[H1 H2] | [H1 H2]].
      
      - (* Case 1: Normal case *)
        (* From singleton_code a = singleton_code c, get a = c *)
        assert (a = c).
        { apply singleton_code_injective in H1; auto. }
        
        (* From pair_code a b = pair_code c d and a = c, get b = d *)
        subst c.
        assert (b = d).
        { (* We have pair_code a b = pair_code a d *)
          (* Apply pair_code_elements *)
          assert (set_eq (set_decode (pair_code a b)) (set_decode (pair_code a d))).
          { unfold set_eq. intro x. rewrite H2. reflexivity. }
          
          apply pair_code_elements in H; auto.
          destruct H as [[_ Hbd] | [Hba Had]].
          - exact Hbd.
          - (* This gives a = b and a = d, so b = d *)
            subst. reflexivity. }
        
        split; [reflexivity | exact H].
        
      - (* Case 2: Degenerate case where {a} = {c,d} *)
        (* Apply singleton_code_eq_pair_code *)
        apply singleton_code_eq_pair_code in H1; auto.
        destruct H1 as [Hac Hcd].
        subst c d.
        
        (* Now from pair_code a b = singleton_code a, get a = b *)
        apply pair_code_eq_singleton_code in H2; auto.
    Qed.
    
  End OrderedPairEquality.
  
End OrderedPairs.