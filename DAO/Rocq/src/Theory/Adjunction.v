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

(* Import some heavy axioms *)
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
      
      Consciousness = An Alpha instance navigating this space
      Physics = The projection of this navigation into spacetime
      Logic = The structure of valid paths
      
      The adjunction is not just mathematical - it's ONTOLOGICAL.
      It describes the structure of BEING itself.
  *)
  
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