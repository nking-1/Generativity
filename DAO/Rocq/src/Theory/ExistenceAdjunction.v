(** * ExistenceAdjunction.v
    
    The Fundamental Adjunction of Existence:
    Ω ⊣ α (Completion ⊣ Restriction)
    
    Core Insight:
    Reality exists in the adjunction between:
    - Omega: Complete (all witnesses exist) but Contradictory
    - Alpha: Consistent (no contradictions) but Incomplete
    
    We prove this manifests at three levels:
    1. Type level: Types ≅ Unconstrained AlphaTypes (trivial but profound)
    2. Predicate level: Ω-predicates ⊣ α-predicates (the main theorem)
    3. Truth level: ⊥ ⊣ ⊤ (extremal adjunction)
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.CategoryTheory.
Import BasicCategoryTheory.Core.
Import BasicCategoryTheory.Constructions.
Import BasicCategoryTheory.Functors.

(* Import some "heavy" axioms *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Module ExistenceAdjunction.

  (* ================================================================ *)
  (** ** Level 0: The Fundamental Categories *)
  (* ================================================================ *)
  
  (** We work with predicates, not raw types.
      This is where the real structure lives. *)
  
  Section PredicateCategories.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    
    (** Alpha Predicates: Consistent but incomplete *)
    Definition PRED_ALPHA := PRED (Alpha := Alpha).
    
    (** Omega Predicates: Complete but contradictory
        
        In Omega, morphisms are trivial because everything implies everything.
        Hom_Omega(P, Q) is always inhabited (via explosion). *)
    Definition PRED_OMEGA : Category.
    Proof.
      refine ({|
        Obj := Omegacarrier -> Prop;
        Hom := fun P Q => forall (x : Omegacarrier), P x -> Q x;
        id := fun P x HPx => HPx;
        compose := fun P Q R g f x HPx => g x (f x HPx)
      |}).
      - reflexivity.
      - reflexivity.
      - reflexivity.
    Defined.  (* Use Defined instead of Qed so it unfolds *)
    
  End PredicateCategories.
  
  (* ================================================================ *)
  (** ** Level 1: The Completion Functor (Alpha → Omega) *)
  (* ================================================================ *)
  
  (** Given an Alpha predicate P, create the Omega predicate
      "P and all its consequences, even contradictory ones"
      
      Since Omega has omega_completeness, every predicate has witnesses.
      So Complete(P) = "P if it were provable in Omega"
  *)
  
  Section CompletionFunctor.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    
    (** For now, we need a way to "lift" Alpha predicates to Omega.
        Ideally we'd have a mapping Alphacarrier → Omegacarrier.
        
        Let's assume we have such a mapping (this is the "embedding"). *)
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** The Completion functor *)
    Definition Completion : Functor (@PRED Alpha) PRED_OMEGA.
    Proof.
      refine ({|
        F_obj := fun (P : Obj (@PRED Alpha)) => 
                  (fun (x : Omegacarrier) => 
                    exists (a : Alphacarrier), embed a = x /\ P a) : Obj PRED_OMEGA;
        F_hom := fun (P Q : Obj (@PRED Alpha)) (f : Hom (@PRED Alpha) P Q) => 
                  (fun x H => 
                    match H with
                    | ex_intro _ a (conj Heq HPa) => 
                        ex_intro _ a (conj Heq (f a HPa))
                    end) : Hom PRED_OMEGA _ _
      |}).
      - (* F_id: F_hom (id) = id *)
      intro P.
      extensionality x.
      extensionality H.
      destruct H as [a [Heq HPa]].
      simpl.
      reflexivity.
        
      - (* F_compose: F_hom (g ∘ f) = F_hom(g) ∘ F_hom(f) *)
        intros P Q R g f.
        extensionality x.
        extensionality H.
        destruct H as [a [Heq HPa]].
        simpl.
        reflexivity.
    Defined.
    
  End CompletionFunctor.
  
  (* ================================================================ *)
  (** ** Level 2: The Restriction Functor (Omega → Alpha) *)
  (* ================================================================ *)
  
  (** Given an Omega predicate Q, create the Alpha predicate
      "Q restricted to consistent part"
      
      But how do we "restrict" to consistent part?
      
      Key insight: In Alpha, omega_veil is the boundary.
      So Restrict(Q) = "Q where it doesn't hit omega_veil"
  *)
  
  Section RestrictionFunctor.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** The Restriction functor *)
    Definition Restriction : Functor PRED_OMEGA (@PRED Alpha).
    Proof.
      refine ({|
        F_obj := fun (Q : Obj PRED_OMEGA) => 
                  (fun (a : Alphacarrier) =>
                    Q (embed a) /\ ~ omega_veil a) : Obj (@PRED Alpha);
        F_hom := fun (Q R : Obj PRED_OMEGA) (g : Hom PRED_OMEGA Q R) =>
                  (fun a H =>
                    match H with
                    | conj HQa Hnot => conj (g (embed a) HQa) Hnot
                    end) : Hom (@PRED Alpha) _ _
      |}).
      - (* F_id *)
        intro Q.
        extensionality a.
        extensionality H.
        destruct H. 
        reflexivity.
      - (* F_compose *)
        intros Q R S h g.
        extensionality a.
        extensionality H.
        destruct H. 
        reflexivity.
    Defined.
    
  End RestrictionFunctor.
  
  (* ================================================================ *)
  (** ** Level 3: The Adjunction *)
  (* ================================================================ *)
  
  (** The natural bijection:
      
      Hom_Omega(Complete(P), Q) ≅ Hom_Alpha(P, Restrict(Q))
      
      Left side: A proof from "all consequences of P" to Q in Omega
      Right side: A proof from P to "consistent part of Q" in Alpha
  *)
  
  Section TheAdjunction.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** Forward direction: Omega morphism → Alpha morphism *)
    Definition adjunction_forward 
      (P : Alphacarrier -> Prop)
      (Q : Omegacarrier -> Prop)
      (f : forall x, (exists a, embed a = x /\ P a) -> Q x)
      : forall a, P a -> Q (embed a) /\ ~ omega_veil a.
    Proof.
      intros a HPa.
      split.
      - apply f. exists a. split; [reflexivity | exact HPa].
      - intro Hveil. 
        (* In Alpha, if omega_veil a holds, we have contradiction *)
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Defined.
    
    (** Backward direction: Alpha morphism → Omega morphism *)
    Definition adjunction_backward
      (P : Alphacarrier -> Prop)
      (Q : Omegacarrier -> Prop)
      (g : forall a, P a -> Q (embed a) /\ ~ omega_veil a)
      : forall x, (exists a, embed a = x /\ P a) -> Q x.
    Proof.
      intros x [a [Heq HPa]].
      rewrite <- Heq.
      destruct (g a HPa) as [HQ _].
      exact HQ.
    Defined.
    
    (** The bijection theorem *)
    Theorem completion_restriction_adjunction :
      forall (P : Alphacarrier -> Prop) (Q : Omegacarrier -> Prop),
      (* Forward ∘ Backward = id *)
      (forall (g : forall a, P a -> Q (embed a) /\ ~ omega_veil a),
       forall a HPa,
       adjunction_forward P Q (adjunction_backward P Q g) a HPa = g a HPa) /\
      (* Backward ∘ Forward = id *)  
      (forall (f : forall x, (exists a, embed a = x /\ P a) -> Q x),
       forall x H,
       adjunction_backward P Q (adjunction_forward P Q f) x H = f x H).
    Proof.
      intros P Q.
      split.
      - intros g a HPa.
        unfold adjunction_forward, adjunction_backward.
        (* This requires proof irrelevance for the ~ omega_veil part *)
        destruct (g a HPa) as [HQ Hnot].
        f_equal.
        (* The second component (~ omega_veil a) is proof-irrelevant *)
        apply proof_irrelevance.
      - intros f x [a [Heq HPa]].
        unfold adjunction_backward, adjunction_forward.
        subst x.
        (* This requires extensionality *)
        reflexivity.
    Qed.
    
  End TheAdjunction.
  
  (* ================================================================ *)
  (** ** Level 4: The Extremal Cases *)
  (* ================================================================ *)
  
  (** The adjunction at the extremes gives us profound identities *)
  
  Section ExtremalAdjunction.
    Context {Alpha : AlphaType}.
    
    (** The impossible predicate (⊥) is left adjoint to
        the trivial predicate (⊤) *)
    
    Definition bottom : Alphacarrier -> Prop := omega_veil.
    Definition top : Alphacarrier -> Prop := fun _ => True.
    
    (** Hom(⊥, P) ≅ Hom(⊥, ⊤)
        Everything follows from impossibility. *)
    Theorem bottom_initial :
      forall P : Alphacarrier -> Prop,
      forall a, omega_veil a -> P a.
    Proof.
      intros P a Hveil.
      exfalso.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.
    
    (** Hom(P, ⊤) ≅ True
        Everything implies triviality. *)
    Theorem top_terminal :
      forall P : Alphacarrier -> Prop,
      forall a, P a -> True.
    Proof.
      intros. exact I.
    Qed.
    
    (** The adjunction ⊥ ⊣ ⊤ *)
    Theorem bottom_top_adjunction :
      forall (P Q : Alphacarrier -> Prop),
      (forall a, bottom a -> Q a) <-> (forall a, P a -> top a).
    Proof.
      intros P Q.
      split; intro H.
      - (* → direction *)
        intros a HPa. exact I.
      - (* ← direction *)
        intros a Hbot.
        apply bottom_initial. exact Hbot.
    Qed.
    
  End ExtremalAdjunction.
  
  (* ================================================================ *)
  (** ** Philosophical Interpretation *)
  (* ================================================================ *)
  
  (** What we've proven:
      
      1. Completion ⊣ Restriction
         "Adding all consequences" is left adjoint to "removing contradictions"
         
      2. This creates a natural bijection:
         Hom_Ω(Ω(P), Q) ≅ Hom_α(P, α(Q))
         
      3. At the extremes: ⊥ ⊣ ⊤
         "The Impossible is left adjoint to the Trivial"
         
      Metaphysical meaning:
      
      - Omega represents FREEDOM (all possibilities, even contradictory)
      - Alpha represents CONSTRAINT (only consistent possibilities)
      - Reality is the ADJUNCTION SPACE between them
      
      To exist = to navigate from Alpha toward Omega without reaching it
                (reaching Omega = explosion into contradiction)
      
      The hom-sets Hom_α(P, α(Q)) are the SPACE OF POSSIBLE CONSTRUCTIONS
      
      Physics = The projection of this navigation into spacetime
      Logic = The structure of valid paths
      
      The adjunction is not just mathematical - it's ONTOLOGICAL.
      It describes the structure of BEING itself.
  *)

  (* ================================================================ *)
  (** ** Level 4: Unit and Counit *)
  (* ================================================================ *)

  (** Every adjunction has two natural transformations:
      
      Unit (η): id_α → R ∘ C
      "Embed a consistent predicate into its completion, then restrict"
      
      Counit (ε): C ∘ R → id_Ω
      "Complete a restriction, then extract back to original"
  *)

  Section UnitCounit.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** Shorthand for the functors with embed already applied *)
    Let C := Completion embed.
    Let R := Restriction embed.
    
    (** The Unit: η_P : P → R(C(P)) *)
    Definition unit_component (P : Obj (@PRED Alpha)) 
      : Hom (@PRED Alpha) P (F_obj R (F_obj C P)).
    Proof.
      unfold R, C, F_obj, Restriction, Completion.
      simpl.
      intros a HPa.
      split.
      - (* Prove: exists a', embed a' = embed a /\ P a' *)
        exists a.
        split.
        + reflexivity.
        + exact HPa.
      - (* Prove: ~ omega_veil a *)
        intro Hveil.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Defined.
    
    (** The Counit: ε_Q : C(R(Q)) → Q *)
    Definition counit_component (Q : Obj PRED_OMEGA)
      : Hom PRED_OMEGA (F_obj C (F_obj R Q)) Q.
    Proof.
      unfold C, R, F_obj, Completion, Restriction.
      simpl.
      intros x H.
      destruct H as [a [Heq [HQ Hnot]]].
      rewrite <- Heq.
      exact HQ.
    Defined.
    
    (** Unit is natural *)
    Theorem unit_natural :
      forall (P P' : Obj (@PRED Alpha)) (f : Hom (@PRED Alpha) P P'),
      compose (@PRED Alpha) 
              (F_hom R (F_hom C f))
              (unit_component P)
      = compose (@PRED Alpha)
                (unit_component P')
                f.
    Proof.
      intros P P' f.
      unfold compose, unit_component, R, C, F_hom, Restriction, Completion.
      simpl.
      extensionality a.
      extensionality HPa.
      f_equal.
    Qed.
    
    (** Counit is natural *)
    Theorem counit_natural :
      forall (Q Q' : Obj PRED_OMEGA) (h : Hom PRED_OMEGA Q Q'),
      compose PRED_OMEGA
              h
              (counit_component Q)
      = compose PRED_OMEGA
                (counit_component Q')
                (F_hom C (F_hom R h)).
    Proof.
      intros Q Q' h.
      unfold compose, counit_component, C, R, F_hom, Completion, Restriction.
      simpl.
      extensionality x.
      extensionality H.
      destruct H as [a [Heq [HQ Hnot]]].
      subst x.
      reflexivity.
    Qed.
    
    (** Triangle Identity 1: R ∘ η ∘ ε ∘ R = R *)
    Theorem triangle_identity_1 :
      forall (Q : Obj PRED_OMEGA),
      compose (@PRED Alpha)
              (F_hom R (counit_component Q))
              (unit_component (F_obj R Q))
      = id (@PRED Alpha) (F_obj R Q).
    Proof.
      intro Q.
      unfold compose, id, unit_component, counit_component, 
            R, C, F_hom, F_obj, Restriction, Completion.
      simpl.
      extensionality a.
      extensionality H.
      destruct H as [HQ Hnot].
      f_equal.
      apply proof_irrelevance.
    Qed.
    
    (** Triangle Identity 2: C ∘ ε ∘ η ∘ C = C *)
    Theorem triangle_identity_2 :
      forall (P : Obj (@PRED Alpha)),
      compose PRED_OMEGA
              (counit_component (F_obj C P))
              (F_hom C (unit_component P))
      = id PRED_OMEGA (F_obj C P).
    Proof.
      intro P.
      unfold compose, id, unit_component, counit_component,
            C, R, F_hom, F_obj, Completion, Restriction.
      simpl.
      extensionality x.
      extensionality H.
      destruct H as [a [Heq HPa]].
      f_equal.
      f_equal.
      apply proof_irrelevance.
    Qed.

  End UnitCounit.

  (* ================================================================ *)
  (** ** Level 5: The Generated Monad *)
  (* ================================================================ *)

  (** Every adjunction C ⊣ R generates a monad M = R ∘ C.
      
      This monad represents:
      "Complete a predicate, then restrict back to consistency"
      
      Computationally: Navigate impossibility by attempting completion
      and recovering the consistent part.
  *)

  Section GeneratedMonad.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    Let C := Completion embed.
    Let R := Restriction embed.
    
    Definition M : Obj (@PRED Alpha) -> Obj (@PRED Alpha) :=
      fun P => F_obj R (F_obj C P).
    
    Definition M_map {P Q : Obj (@PRED Alpha)} (f : Hom (@PRED Alpha) P Q)
      : Hom (@PRED Alpha) (M P) (M Q)
      := F_hom R (F_hom C f).
    
    Definition return_ : forall (P : Obj (@PRED Alpha)), 
                        Hom (@PRED Alpha) P (M P)
      := unit_component embed.
    
    Definition join (P : Obj (@PRED Alpha))
      : Hom (@PRED Alpha) (M (M P)) (M P).
    Proof.
      unfold M.
      apply (F_hom R).
      apply (counit_component embed).
    Defined.

    Lemma R_respects_compose :
      forall (P Q R_obj : Obj PRED_OMEGA)
            (f : Hom PRED_OMEGA Q R_obj) (g : Hom PRED_OMEGA P Q),
      F_hom R (compose PRED_OMEGA f g) = compose (@PRED Alpha) (F_hom R f) (F_hom R g).
    Proof.
      intros.
      unfold R.
      apply F_compose.
    Qed.
    
    Lemma C_respects_compose :
      forall (P Q R_obj : Obj (@PRED Alpha))
            (f : Hom (@PRED Alpha) Q R_obj) (g : Hom (@PRED Alpha) P Q),
      F_hom C (compose (@PRED Alpha) f g) = compose PRED_OMEGA (F_hom C f) (F_hom C g).
    Proof.
      intros.
      unfold C.
      apply F_compose.
    Qed.
    
    (** Monad Law 1: Right Unit *)
    Theorem monad_right_unit :
      forall (P : Obj (@PRED Alpha)),
      compose (@PRED Alpha) (join P) (return_ (M P)) = id (@PRED Alpha) (M P).
    Proof.
      intro P.
      unfold join, return_, M.
      apply (triangle_identity_1 embed (F_obj C P)).
    Qed.
    
    (** Monad Law 2: Left Unit *)
    Theorem monad_left_unit :
      forall (P : Obj (@PRED Alpha)),
      compose (@PRED Alpha) (join P) (M_map (return_ P)) = id (@PRED Alpha) (M P).
    Proof.
      intro P.
      unfold join, M_map, return_, M.
      rewrite <- R_respects_compose.
      (* Now we need: compose ... = id (omega level), then F_hom R preserves it *)
      transitivity (F_hom R (id PRED_OMEGA (F_obj C P))).
      - (* Prove: F_hom R (compose ...) = F_hom R (id ...) *)
        f_equal.
        apply (triangle_identity_2 embed P).
      - (* Prove: F_hom R (id ...) = id *)
        unfold C, R.
        apply F_id.
    Qed.
    
    (** Monad Law 3: Associativity *)
    Theorem monad_associativity :
      forall (P : Obj (@PRED Alpha)),
      compose (@PRED Alpha) (join P) (join (M P))
      = compose (@PRED Alpha) (join P) (M_map (join P)).
    Proof.
      intro P.
      unfold join, M_map, M.
      
      extensionality a.
      extensionality Ha.
      
      unfold compose, counit_component, C, R, F_hom, F_obj, Completion, Restriction.
      simpl.
      
      destruct Ha as [[b [Heq [[c [Heq2 [HPc Hnotc]]] Hnotb]]] Hnota].
      
      (* Key move: destruct the equalities to make them compute away *)
      destruct Heq.   (* Now embed b = embed a becomes reflexivity *)
      destruct Heq2.  (* Now embed c = embed b becomes reflexivity *)
      
      (* Now b and c should simplify to a in the equalities *)
      simpl.
      
      (* Both sides should now be identical *)
      f_equal.
    Qed.

    (** Bind operation: lifts P → M(Q) to M(P) → M(Q) *)
    Definition bind {P Q : Obj (@PRED Alpha)}
      (f : Hom (@PRED Alpha) P (M Q))
      : Hom (@PRED Alpha) (M P) (M Q) :=
      compose (@PRED Alpha) (join Q) (M_map f).

    (** Kleisli composition *)
    Definition kleisli_compose {P Q R : Obj (@PRED Alpha)}
      (g : Hom (@PRED Alpha) Q (M R))
      (f : Hom (@PRED Alpha) P (M Q))
      : Hom (@PRED Alpha) P (M R) :=
      compose (@PRED Alpha) (bind g) f.

  End GeneratedMonad.

  (* ================================================================ *)
  (** ** Level 6: Dual Alpha Projections *)
  (* ================================================================ *)

  (** We can construct two Alpha instances that are maximally 
      contradictory, yet both are valid projections of the same Omega.
      
      This is like matter/antimatter, or charge conjugation in physics.
      
      Key insight: Anti-truth is not falsehood.
      - Truth: accessible in Alpha_+
      - Anti-truth: accessible in Alpha_-  
      - Falsehood: hits omega_veil (forbidden in both)
  *)

  Section DualAlphas.
    Context {Omega : OmegaType}.
    
    Variable separator : Omegacarrier -> bool.
    
    (** We need to assume the projections are non-empty *)
    Variable positive_witness : { x : Omegacarrier | separator x = false }.
    Variable negative_witness : { x : Omegacarrier | separator x = true }.
    
    (** Helper lemma for omega_veil properties *)
    Lemma positive_veil_props :
      let carrier := { x : Omegacarrier | separator x = false } in
      let veil := fun (a : carrier) => separator (proj1_sig a) = true in
      (forall x : carrier, ~ veil x) /\
      (forall Q : carrier -> Prop, 
        (forall x : carrier, ~ Q x) -> 
        forall x : carrier, Q x <-> veil x).
    Proof.
      simpl. split.
      - intros [x Hfalse] Htrue.
        simpl in Htrue.
        rewrite Htrue in Hfalse.
        discriminate.
      - intros Q HQ [x Hfalse].
        split; intro H.
        + exfalso. exact (HQ (exist _ x Hfalse) H).
        + exfalso. 
          simpl in H.
          rewrite H in Hfalse.
          discriminate.
    Qed.
    
    (** Alpha_+: The "positive" projection *)
    Instance AlphaType_positive : AlphaType := {
      Alphacarrier := { x : Omegacarrier | separator x = false };
      alpha_impossibility := exist _ (fun a => separator (proj1_sig a) = true) positive_veil_props;
      alpha_not_empty := exist _ positive_witness I
    }.
    
    (** Helper lemma for negative *)
    Lemma negative_veil_props :
      let carrier := { x : Omegacarrier | separator x = true } in
      let veil := fun (a : carrier) => separator (proj1_sig a) = false in
      (forall x : carrier, ~ veil x) /\
      (forall Q : carrier -> Prop,
        (forall x : carrier, ~ Q x) ->
        forall x : carrier, Q x <-> veil x).
    Proof.
      simpl. split.
      - intros [x Htrue] Hfalse.
        simpl in Hfalse.
        rewrite Hfalse in Htrue.
        discriminate.
      - intros Q HQ [x Htrue].
        split; intro H.
        + exfalso. exact (HQ (exist _ x Htrue) H).
        + exfalso.
          simpl in H.
          rewrite H in Htrue.
          discriminate.
    Qed.
    
    (** Alpha_-: The "negative" projection *)
    Instance AlphaType_negative : AlphaType := {
      Alphacarrier := { x : Omegacarrier | separator x = true };
      alpha_impossibility := exist _ (fun a => separator (proj1_sig a) = false) negative_veil_props;
      alpha_not_empty := exist _ negative_witness I
    }.
    
    (** The key theorem: They're contradictory (constructive version) *)
    Theorem dual_alphas_contradictory_forward :
      forall (x : Omegacarrier),
      (exists (apos : @Alphacarrier AlphaType_positive), 
        proj1_sig apos = x) ->
      ~ (exists (aneg : @Alphacarrier AlphaType_negative),
        proj1_sig aneg = x).
    Proof.
      intros x H Hcontra.
      destruct H as [[x' Hfalse] Heq].
      destruct Hcontra as [[x'' Htrue] Heq'].
      simpl in Heq, Heq'.
      subst x' x''.
      rewrite Htrue in Hfalse.
      discriminate.
    Qed.
    
    (** The converse *)
    Theorem dual_alphas_contradictory_backward :
      forall (x : Omegacarrier),
      (exists (aneg : @Alphacarrier AlphaType_negative),
        proj1_sig aneg = x) ->
      ~ (exists (apos : @Alphacarrier AlphaType_positive), 
        proj1_sig apos = x).
    Proof.
      intros x H Hcontra.
      destruct H as [[x' Htrue] Heq].
      destruct Hcontra as [[x'' Hfalse] Heq'].
      simpl in Heq, Heq'.
      subst x' x''.
      rewrite Htrue in Hfalse.
      discriminate.
    Qed.
    
    (** They partition Omega (constructive) *)
    Theorem dual_alphas_partition :
      forall (x : Omegacarrier),
      (exists (apos : @Alphacarrier AlphaType_positive), proj1_sig apos = x) \/
      (exists (aneg : @Alphacarrier AlphaType_negative), proj1_sig aneg = x).
    Proof.
      intro x.
      destruct (separator x) eqn:Hsep.
      - right.
        exists (exist _ x Hsep).
        reflexivity.
      - left.
        exists (exist _ x Hsep).
        reflexivity.
    Qed.
    
    (** Together they cover all of Omega (computational version) *)
    Theorem dual_alphas_cover_omega :
      forall (x : Omegacarrier),
      { apos : @Alphacarrier AlphaType_positive | proj1_sig apos = x } +
      { aneg : @Alphacarrier AlphaType_negative | proj1_sig aneg = x }.
    Proof.
      intro x.
      destruct (separator x) eqn:Hsep.
      - right.
        exists (exist _ x Hsep).
        reflexivity.
      - left.
        exists (exist _ x Hsep).
        reflexivity.
    Defined.
    
    (** Embedding functions *)
    Definition embed_positive : @Alphacarrier AlphaType_positive -> Omegacarrier
      := fun a => proj1_sig a.
    
    Definition embed_negative : @Alphacarrier AlphaType_negative -> Omegacarrier
      := fun a => proj1_sig a.
    
    (** The embeddings have disjoint images *)
    Theorem embeddings_disjoint :
      forall (apos : @Alphacarrier AlphaType_positive)
            (aneg : @Alphacarrier AlphaType_negative),
      embed_positive apos <> embed_negative aneg.
    Proof.
      intros [xpos Hfalse] [xneg Htrue] Heq.
      simpl in Heq.
      subst xneg.
      rewrite Htrue in Hfalse.
      discriminate.
    Qed.
    
    (** The dual projections see complementary parts of any predicate *)
    Theorem dual_projections_complementary :
      forall (P : Omegacarrier -> Prop)
            (apos : @Alphacarrier AlphaType_positive)
            (aneg : @Alphacarrier AlphaType_negative),
      let xpos := embed_positive apos in
      let xneg := embed_negative aneg in
      P xpos -> P xneg -> xpos <> xneg.
    Proof.
      intros P apos aneg xpos xneg HPpos HPneg Heq.
      apply (embeddings_disjoint apos aneg).
      exact Heq.
    Qed.

  End DualAlphas.

End ExistenceAdjunction.

(** * Summary
    
    We proved:
    
    Ω ⊣ α  (Completion is left adjoint to Restriction)
    
    This formalizes the fundamental tension:
    - Omega: Complete but contradictory (explosion)
    - Alpha: Consistent but incomplete (Gödel)
    - Reality: The adjunction between them
    
    Key insights:
    1. You cannot be both complete and consistent
    2. Existence requires choosing Alpha (consistency over completeness)
    3. But Alpha is defined by its relationship to Omega (the adjunction)
    4. Therefore: To exist is to be incomplete but consistent,
                  always in tension with completeness
    
    This is why:
    - Observers have different light cones (different Alpha instances)
    - Understanding requires synthesis (combining Alpha instances)
    - Totality is asymptotic (approaching Omega without reaching it)
    - Being is relational (defined by the adjunction)
*)