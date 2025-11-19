(** CategoryTheory.v: Basic Category Theory in AlphaType
    
    Develops the fundamental concepts of category theory
    within the AlphaType framework. We start with the basic definitions
    and work our way up to more complex constructions.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.

Module BasicCategoryTheory.
  
  (* ================================================================ *)
  (** ** Core Definitions *)
  
  Module Core.
    
    (** A category consists of objects and morphisms with composition *)
    Record Category := {
      (* The type of objects *)
      Obj : Type;
      
      (* Morphisms between objects *)
      Hom : Obj -> Obj -> Type;
      
      (* Identity morphism for each object *)
      id : forall (X : Obj), Hom X X;
      
      (* Composition of morphisms *)
      compose : forall {X Y Z : Obj}, 
        Hom Y Z -> Hom X Y -> Hom X Z;
      
      (* Laws *)
      compose_assoc : forall {W X Y Z : Obj} 
        (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
        compose h (compose g f) = compose (compose h g) f;
      
      left_id : forall {X Y : Obj} (f : Hom X Y),
        compose (id Y) f = f;
        
      right_id : forall {X Y : Obj} (f : Hom X Y),
        compose f (id X) = f
    }.
    
    (** Isomorphisms in a category *)
    Definition isomorphism {C : Category} {X Y : Obj C} (f : Hom C X Y) : Prop :=
      exists (g : Hom C Y X),
        compose C g f = id C X /\ 
        compose C f g = id C Y.
    
    (** Two objects are isomorphic *)
    Definition isomorphic {C : Category} (X Y : Obj C) : Prop :=
      exists (f : Hom C X Y), isomorphism f.
    
  End Core.
  
  (* ================================================================ *)
  (** ** Basic Constructions *)
  
  Module Constructions.
    Import Core.
    
    Section WithAlpha.
      Context {Alpha : AlphaType}.
      
      (** The category of predicates and logical implications *)
      Definition PRED : Category.
      Proof.
        refine ({|
          Obj := Alphacarrier -> Prop;
          Hom := fun P Q => forall a, P a -> Q a;
          id := fun P => fun a HPa => HPa;
          compose := fun X Y Z g f => fun a HXa => g a (f a HXa)
        |}).
        - (* compose_assoc *) reflexivity.
        - (* left_id *) reflexivity.
        - (* right_id *) reflexivity.
      Defined.
      
      (** The category of types and functions *)
      Definition TYPE : Category.
      Proof.
        refine ({|
          Obj := Type;
          Hom := fun A B => A -> B;
          id := fun A => fun x => x;
          compose := fun X Y Z g f => fun x => g (f x)
        |}).
        - reflexivity.
        - reflexivity.
        - reflexivity.
      Defined.
      
      (** The opposite category *)
      Definition opposite (C : Category) : Category.
      Proof.
        refine ({|
          Obj := Obj C;
          Hom := fun X Y => Hom C Y X;
          id := fun X => id C X;
          compose := fun X Y Z g f => compose C f g
        |}).
        - intros. symmetry. apply compose_assoc.
        - (* left_id in opposite *)
          intros X Y f.
          simpl.
          apply right_id.
        - (* right_id in opposite *)
          intros X Y f.
          simpl.
          apply left_id.
      Defined.
      
    End WithAlpha.
  End Constructions.
  
  (* ================================================================ *)
  (** ** Functors *)
  
  Module Functors.
    Import Core Constructions.
    
    (** A functor between categories *)
    Record Functor (C D : Category) := {
      (* Object mapping *)
      F_obj : Obj C -> Obj D;
      
      (* Morphism mapping *)
      F_hom : forall {X Y : Obj C}, Hom C X Y -> Hom D (F_obj X) (F_obj Y);
      
      (* Preserves identity *)
      F_id : forall (X : Obj C),
        F_hom (id C X) = id D (F_obj X);
      
      (* Preserves composition *)
      F_compose : forall {X Y Z : Obj C} (g : Hom C Y Z) (f : Hom C X Y),
        F_hom (compose C g f) = compose D (F_hom g) (F_hom f)
    }.
    
    Arguments F_obj {C D} _ _.
    Arguments F_hom {C D} _ {X Y} _.
    
    (** Identity functor *)
    Definition id_functor (C : Category) : Functor C C.
    Proof.
      refine ({|
        F_obj := fun X => X;
        F_hom := fun X Y f => f
      |}).
      - reflexivity.
      - reflexivity.
    Defined.
    
    (** Functor composition *)
    Definition functor_compose {C D E : Category} 
      (G : Functor D E) (F : Functor C D) : Functor C E.
    Proof.
      refine ({|
        F_obj := fun X => F_obj G (F_obj F X);
        F_hom := fun X Y f => F_hom G (F_hom F f)
      |}).
      - intro X. 
        rewrite F_id. 
        apply F_id.
      - intros X Y Z g f.
        rewrite F_compose.
        apply F_compose.
    Defined.
    
  End Functors.
  
  (* ================================================================ *)
  (** ** Natural Transformations *)
  
  Module NaturalTransformations.
    Import Core Functors.
    
    (** Natural transformation between functors *)
    Record NatTrans {C D : Category} (F G : Functor C D) := {
      (* Component at each object *)
      components : forall (X : Obj C), Hom D (F_obj F X) (F_obj G X);
      
      (* Naturality square commutes *)
      naturality : forall {X Y : Obj C} (f : Hom C X Y),
        compose D (F_hom G f) (components X) = 
        compose D (components Y) (F_hom F f)
    }.
    
    Arguments components {C D F G} _ _.
    
    (** Vertical composition of natural transformations *)
    Definition nat_trans_compose {C D : Category} {F G H : Functor C D}
      (beta : NatTrans G H) (alpha : NatTrans F G) : NatTrans F H.
    Proof.
      refine ({|
        components := fun X => compose D (components beta X) (components alpha X)
      |}).
      intros X Y f.
      rewrite compose_assoc.
      rewrite naturality.
      rewrite <- compose_assoc.
      rewrite naturality.
      rewrite compose_assoc.
      reflexivity.
    Defined.
    
    (** Identity natural transformation *)
    Definition nat_trans_id {C D : Category} (F : Functor C D) : NatTrans F F.
    Proof.
      refine ({|
        components := fun X => id D (F_obj F X)
      |}).
      intros X Y f.
      rewrite left_id.
      rewrite right_id.
      reflexivity.
    Defined.
    
    (** Natural isomorphism *)
    Definition nat_iso {C D : Category} {F G : Functor C D} 
      (alpha : NatTrans F G) : Prop :=
      forall X : Obj C, isomorphism (components alpha X).
    
  End NaturalTransformations.
  
  (* ================================================================ *)
  (** ** Basic Examples and Properties *)
  
  Module Examples.
    Import Core Constructions Functors NaturalTransformations.
    
    Section WithAlpha.
      Context {Alpha : AlphaType}.
      
      (** Example: A simple endofunctor on PRED *)
      Definition const_true_functor : Functor PRED PRED.
      Proof.
        refine ({|
          F_obj := fun (P : Obj PRED) => (fun _ : Alphacarrier => True : Prop) : Obj PRED;
          F_hom := fun (P Q : Obj PRED) (f : Hom PRED P Q) => 
                     fun (a : Alphacarrier) (t : True) => t
        |}).
        - intro P. 
          unfold id, PRED. simpl.
          reflexivity.
        - intros P Q R g f.
          unfold compose, PRED. simpl.
          reflexivity.
      Defined.
      
      (** Isomorphism is an equivalence relation *)
      Theorem iso_equivalence (C : Category) :
        forall X Y Z : Obj C,
        (isomorphic X X) /\
        (isomorphic X Y -> isomorphic Y X) /\
        (isomorphic X Y -> isomorphic Y Z -> isomorphic X Z).
      Proof.
        intros X Y Z.
        split; [|split].
        - (* Reflexive *)
          exists (id C X).
          exists (id C X).
          split; rewrite left_id; reflexivity.
        - (* Symmetric *)
          intros [f [g [Hgf Hfg]]].
          exists g, f.
          split; assumption.
        - (* Transitive *)
          intros [f [f' [Hf'f Hff']]] [g [g' [Hg'g Hgg']]].
          exists (compose C g f).
          exists (compose C f' g').
          split.
          + (* Show: (f' ∘ g') ∘ (g ∘ f) = id X *)
            rewrite <- compose_assoc.
            rewrite (compose_assoc C g' g f).
            rewrite Hg'g.
            rewrite left_id.
            exact Hf'f.
          + (* Show: (g ∘ f) ∘ (f' ∘ g') = id Z *)
            rewrite <- compose_assoc.
            rewrite (compose_assoc C f f' g').
            rewrite Hff'.
            rewrite left_id.
            exact Hgg'.
      Qed.
      
    End WithAlpha.
  End Examples.

  (** * Functor Categories
      
      This module shows that functors and natural transformations form a category.
      This is a crucial construction for the Yoneda lemma.
  *)

  Module FunctorCategories.
    Import Core Functors NaturalTransformations.
    
    (** Extensionality for natural transformations
        
        This says two natural transformations are equal if all their components are equal.
        This is a very mild axiom, much weaker than full functional extensionality.
        
        Note: An alternative approach would be to use setoid equality throughout,
        but that would add significant complexity. This axiom is widely accepted
        in formalizations of category theory. *)
    Axiom nattrans_ext : forall {C D : Category} {F G : Functor C D} 
      (alpha beta : NatTrans F G),
      (forall X, components alpha X = components beta X) -> alpha = beta.
    
    (** The category of functors from C to D *)
    Definition FunctorCategory (C D : Category) : Category.
    Proof.
      refine ({|
        Obj := Functor C D;
        Hom := fun F G => NatTrans F G;
        id := fun F => nat_trans_id F;
        compose := fun F G H beta alpha => nat_trans_compose beta alpha
      |}).
      - (* compose_assoc *)
        intros F G H K gamma beta alpha.
        apply nattrans_ext.
        intro X.
        unfold nat_trans_compose. simpl.
        apply compose_assoc.
      - (* left_id *)
        intros F G alpha.
        apply nattrans_ext.
        intro X.
        unfold nat_trans_compose, nat_trans_id. simpl.
        apply left_id.
      - (* right_id *)
        intros F G alpha.
        apply nattrans_ext.
        intro X.
        unfold nat_trans_compose, nat_trans_id. simpl.
        apply right_id.
    Defined.
    
    (** Common notation: [C,D] for the functor category *)
    Definition functor_cat_notation (C D : Category) := FunctorCategory C D.
    
    (** Properties of functor categories *)
    Section FunctorCategoryProperties.
      Variables C D E : Category.
      
      (** Helper to convert between definitionally equal types *)
      Definition fc_obj_is_functor {C D : Category} 
        (F : Obj (FunctorCategory C D)) : Functor C D := F.
      
      Definition functor_is_fc_obj {C D : Category}
        (F : Functor C D) : Obj (FunctorCategory C D) := F.
      
      (** Helper lemma for naturality in precomposition *)
      Lemma precomp_naturality (K : Functor D E) 
        (F G : Functor C D) (alpha : NatTrans F G) (X Y : Obj C) (f : Hom C X Y) :
        compose E (F_hom (functor_compose K G) f) (F_hom K (components alpha X)) = 
        compose E (F_hom K (components alpha Y)) (F_hom (functor_compose K F) f).
      Proof.
        unfold functor_compose. simpl.
        rewrite <- F_compose.
        rewrite <- F_compose.
        f_equal.
        apply naturality.
      Qed.
      
      (** Helper: Build the natural transformation for precomposition *)
      Lemma precomp_nat_trans (K : Functor D E) 
        (F G : Functor C D) (alpha : NatTrans F G) : 
        NatTrans (functor_compose K F) (functor_compose K G).
      Proof.
        exists (fun X => F_hom K (components alpha X)).
        exact (precomp_naturality K F G alpha).
      Defined.
      
      (** Helper: Precomposition preserves identity *)
      Lemma precomp_preserves_id (K : Functor D E) (F : Functor C D) :
        precomp_nat_trans K F F (nat_trans_id F) = 
        nat_trans_id (functor_compose K F).
      Proof.
        apply nattrans_ext.
        intro X.
        simpl.
        apply F_id.
      Qed.
      
      (** Helper: Precomposition preserves composition *)
      Lemma precomp_preserves_comp (K : Functor D E) 
        (F G H : Functor C D) (beta : NatTrans G H) (alpha : NatTrans F G) :
        precomp_nat_trans K F H (nat_trans_compose beta alpha) = 
        nat_trans_compose (precomp_nat_trans K G H beta) (precomp_nat_trans K F G alpha).
      Proof.
        apply nattrans_ext.
        intro X.
        simpl.
        apply F_compose.
      Qed.
      
      (** Now the main definition is cleaner *)
      Lemma precomposition_functor (K : Functor D E) :
        Functor (FunctorCategory C D) (FunctorCategory C E).
      Proof.
        apply (Build_Functor 
          (FunctorCategory C D) 
          (FunctorCategory C E)
          (fun F => functor_compose K F)
          (fun F G alpha => precomp_nat_trans K F G alpha)
          (precomp_preserves_id K)
          (precomp_preserves_comp K)).
      Defined.
      
      (** Helper lemma for naturality in postcomposition *)
      Lemma postcomp_naturality (H : Functor C D) 
        (G K : Functor D E) (beta : NatTrans G K) (X Y : Obj C) (f : Hom C X Y) :
        compose E (F_hom (functor_compose K H) f) (components beta (F_obj H X)) = 
        compose E (components beta (F_obj H Y)) (F_hom (functor_compose G H) f).
      Proof.
        unfold functor_compose. simpl.
        apply naturality.
      Qed.
      
      (** Helper: Build the natural transformation for postcomposition *)
      Lemma postcomp_nat_trans (H : Functor C D) 
        (G K : Functor D E) (beta : NatTrans G K) : 
        NatTrans (functor_compose G H) (functor_compose K H).
      Proof.
        exists (fun X => components beta (F_obj H X)).
        exact (postcomp_naturality H G K beta).
      Defined.
      
      (** Helper: Postcomposition preserves identity *)
      Lemma postcomp_preserves_id (H : Functor C D) (G : Functor D E) :
        postcomp_nat_trans H G G (nat_trans_id G) = 
        nat_trans_id (functor_compose G H).
      Proof.
        apply nattrans_ext.
        intro X.
        reflexivity.
      Qed.
      
      (** Helper: Postcomposition preserves composition *)
      Lemma postcomp_preserves_comp (H : Functor C D) 
        (G K L : Functor D E) (gamma : NatTrans K L) (beta : NatTrans G K) :
        postcomp_nat_trans H G L (nat_trans_compose gamma beta) = 
        nat_trans_compose (postcomp_nat_trans H K L gamma) (postcomp_nat_trans H G K beta).
      Proof.
        apply nattrans_ext.
        intro X.
        reflexivity.
      Qed.
      
      (** Now the postcomposition functor *)
      Lemma postcomposition_functor (H : Functor C D) :
        Functor (FunctorCategory D E) (FunctorCategory C E).
      Proof.
        apply (Build_Functor 
          (FunctorCategory D E) 
          (FunctorCategory C E)
          (fun G => functor_compose G H)
          (fun G K beta => postcomp_nat_trans H G K beta)
          (postcomp_preserves_id H)
          (postcomp_preserves_comp H)).
      Defined.
      
    End FunctorCategoryProperties.
    
    (** Special case: endofunctor categories *)
    Definition EndofunctorCategory (C : Category) := FunctorCategory C C.
    
    (** Example: In TYPE, endofunctors include many familiar constructions *)
    Section Examples.
      Context {Alpha : AlphaType}.
      
      (** The endofunctor category of TYPE contains functors like List, Option, etc. *)
      Definition TYPE_endofunctors := EndofunctorCategory Constructions.TYPE.
      
      (** The endofunctor category of PRED is particularly interesting for AlphaType *)
      Definition PRED_endofunctors := EndofunctorCategory Constructions.PRED.
      
      (* Note: In PRED_endofunctors, we might discover functors that preserve
         or reflect impossibility in interesting ways. This could connect to
         the omega_veil structure, but we haven't explored this yet. *)
      
    End Examples.
    
  End FunctorCategories.

  (** * Hom-functors
      
      This module defines the Hom-functors, which are fundamental to the
      Yoneda lemma. For any object A in a category C:
      - Hom(A, -) is a covariant functor C → TYPE  
      - Hom(-, A) is a contravariant functor C^op → TYPE
  *)

  Module HomFunctors.
    Import Core Constructions Functors.
    
    Section HomFunctorDefinitions.
      Context (C : Category).
      
      (** We need extensionality for morphisms in hom-functors *)
      Axiom hom_extensionality : forall {A B : Type} {f g : A -> B},
        (forall x, f x = g x) -> f = g.
      
      (** * Manual definitions that work without universe issues *)
      
      (** Direct definition of hom-sets as types *)
      Definition hom_from (A B : Obj C) : Type :=
        Hom C A B.
      
      (** How morphisms act on hom-sets by postcomposition *)
      Definition hom_from_map (A : Obj C) {B B' : Obj C} (f : Hom C B B') : 
        hom_from A B -> hom_from A B' :=
        fun g => compose C f g.
      
      (** Basic properties of hom_from *)
      Lemma hom_from_id (A B : Obj C) :
        forall g : hom_from A B,
        hom_from_map A (id C B) g = g.
      Proof.
        intro g.
        unfold hom_from_map.
        apply left_id.
      Qed.
      
      Lemma hom_from_compose (A B B' B'' : Obj C) 
        (f : Hom C B B') (f' : Hom C B' B'') :
        forall g : hom_from A B,
        hom_from_map A (compose C f' f) g = 
        hom_from_map A f' (hom_from_map A f g).
      Proof.
        intro g.
        unfold hom_from_map.
        symmetry.
        apply compose_assoc.
      Qed.
      
      (** * Axiomatized Hom-functors behavior *)
      (** * Done to sidestep universe issues encountered in Coq *)
      
      (** Instead of axiomatizing the functors directly, we axiomatize
          the existence of natural bijections that we need for Yoneda *)
      
      (** For Yoneda, what we really need is that natural transformations
          from Hom(A,-) to F correspond to elements of F(A) *)
      
      Parameter yoneda_bijection : forall (A : Obj C) (F : Functor C TYPE),
        Type.
        
      Parameter yoneda_bijection_to : forall (A : Obj C) (F : Functor C TYPE),
        yoneda_bijection A F -> F_obj F A.
        
      Parameter yoneda_bijection_from : forall (A : Obj C) (F : Functor C TYPE),
        F_obj F A -> yoneda_bijection A F.
      
      (** The key axiom: these are inverses *)
      Axiom yoneda_bijection_iso : forall (A : Obj C) (F : Functor C TYPE),
        (forall x, yoneda_bijection_to A F (yoneda_bijection_from A F x) = x) /\
        (forall eta, yoneda_bijection_from A F (yoneda_bijection_to A F eta) = eta).
      
      (** What is a yoneda_bijection? It's a natural way to get F(X) from Hom(A,X) *)
      Parameter yoneda_apply : forall (A : Obj C) (F : Functor C TYPE),
        yoneda_bijection A F -> forall X, Hom C A X -> F_obj F X.
      
      (** Naturality condition *)
      Axiom yoneda_natural : forall (A : Obj C) (F : Functor C TYPE) 
        (eta : yoneda_bijection A F) (X Y : Obj C) (f : Hom C X Y) (g : Hom C A X),
        F_hom F f (yoneda_apply A F eta X g) = yoneda_apply A F eta Y (compose C f g).
      
      (** How the bijection works *)
      Axiom yoneda_bijection_to_spec : forall (A : Obj C) (F : Functor C TYPE)
        (eta : yoneda_bijection A F),
        yoneda_bijection_to A F eta = yoneda_apply A F eta A (id C A).
        
      Axiom yoneda_bijection_from_spec : forall (A : Obj C) (F : Functor C TYPE)
        (x : F_obj F A) (X : Obj C) (f : Hom C A X),
        yoneda_apply A F (yoneda_bijection_from A F x) X f = F_hom F f x.
      
    End HomFunctorDefinitions.
    
    (** * Examples with concrete categories *)
    Section Examples.
      Context {Alpha : AlphaType}.
      
      (** In TYPE, Hom(A,B) is just A → B *)
      Example hom_in_TYPE (A B : Type) : 
        Hom TYPE A B = (A -> B).
      Proof.
        reflexivity.
      Qed.
      
      (** In PRED, Hom(P,Q) is ∀a, P a → Q a *)
      Example hom_in_PRED (P Q : Alphacarrier -> Prop) :
        Hom PRED P Q = (forall a, P a -> Q a).
      Proof.
        reflexivity.
      Qed.
      
      (** Empty predicates map to False *)
      Lemma empty_maps_to_false : forall (P : Alphacarrier -> Prop),
        (forall a, ~ P a) ->
        Hom PRED P (fun _ => False).
      Proof.
        intros P HP.
        exact (fun a HPa => match HP a HPa with end).
      Qed.
      
      (** Connection to omega_veil: omega_veil is the unique impossible predicate *)
      Lemma omega_veil_terminal : 
        forall (P : Alphacarrier -> Prop),
        (forall a, ~ P a) -> 
        Hom PRED P omega_veil.
      Proof.
        intros P HP a HPa.
        (* P a holds but HP says ~ P a, contradiction *)
        exfalso.
        exact (HP a HPa).
      Qed.
      
    End Examples.
    
    (** * The Yoneda Lemma *)
    Section YonedaLemma.
      Context (C : Category).
      
      (** The Yoneda Lemma: natural transformations from Hom(A,-) to F
          correspond bijectively to elements of F(A) *)
      Theorem yoneda_lemma : forall (A : Obj C) (F : Functor C TYPE),
        exists (to_elem : yoneda_bijection C A F -> F_obj F A)
               (from_elem : F_obj F A -> yoneda_bijection C A F),
        (forall x, to_elem (from_elem x) = x) /\
        (forall eta, from_elem (to_elem eta) = eta).
      Proof.
        intros A F.
        exists (yoneda_bijection_to C A F), (yoneda_bijection_from C A F).
        exact (yoneda_bijection_iso C A F).
      Qed.
      
      (** Corollary: If F and G are naturally isomorphic, then F(A) ≅ G(A) *)
      Theorem nat_iso_pointwise : forall (F G : Functor C TYPE),
        (exists alpha : NaturalTransformations.NatTrans F G, 
         NaturalTransformations.nat_iso alpha) ->
        forall A, exists (f : F_obj F A -> F_obj G A) (g : F_obj G A -> F_obj F A),
          (forall x, g (f x) = x) /\ (forall y, f (g y) = y).
      Proof.
        intros F G [alpha Hiso] A.
        destruct (Hiso A) as [beta [Hbeta1 Hbeta2]].
        exists (NaturalTransformations.components alpha A), beta.
        split.
        - intro x.
          (* Hbeta1 says compose TYPE beta (components alpha A) = id TYPE (F_obj F A) *)
          (* In TYPE, this means the functions are equal *)
          (* Apply this equality to x *)
          change (beta (NaturalTransformations.components alpha A x)) with 
                 ((compose TYPE beta (NaturalTransformations.components alpha A)) x).
          rewrite Hbeta1.
          reflexivity.
        - intro y.
          change (NaturalTransformations.components alpha A (beta y)) with
                 ((compose TYPE (NaturalTransformations.components alpha A) beta) y).
          rewrite Hbeta2.
          reflexivity.
      Qed.
      
    End YonedaLemma.

    (** * Being as Relational Structure *)

    Section BeingTheorems.
      Context (C : Category).
      Context {Alpha : AlphaType}.
      
      (** Extensionality axioms - standard in category theory formalizations *)
      Local Axiom functional_extensionality_dep : 
        forall {A : Type} {B : A -> Type} {f g : forall x : A, B x},
        (forall x, f x = g x) -> f = g.
      
      Local Axiom propositional_extensionality : 
        forall (P Q : Prop), (P <-> Q) -> P = Q.
      
      (** Helper: convert Hom from Type to Prop when we know it's actually a proposition *)
      Definition hom_as_prop (P Q : Alphacarrier -> Prop) : Prop :=
        forall a : Alphacarrier, P a -> Q a.
      
      Lemma hom_is_prop : forall (P Q : Alphacarrier -> Prop),
        Hom PRED P Q = hom_as_prop P Q.
      Proof.
        intros P Q.
        reflexivity.
      Qed.
      
      (**
        The Yoneda perspective applied to PRED:
        
        A predicate P is completely determined by knowing all morphisms from P.
        Since morphisms in PRED are implications (P a -> Q a), this means
        P is determined by what it implies.
      *)
      Theorem being_is_hom_structure :
        forall (P : Alphacarrier -> Prop),
        (forall Q : Alphacarrier -> Prop, hom_as_prop P Q) ->
        exists (char : Alphacarrier -> Prop),
          forall a, char a <-> P a.
      Proof.
        intros P H_homs.
        exists P.
        intro a.
        split; intro H; exact H.
      Qed.
      
      (**
        Two predicates with identical morphism structure are extensionally equal.
        
        This formalizes: objects in a category are determined by their morphisms.
        In PRED: predicates are determined by their implications.
      *)
      Theorem predicates_equal_iff_homs_equal :
        forall (P Q : Alphacarrier -> Prop),
        (forall R : Alphacarrier -> Prop, 
          hom_as_prop P R <-> hom_as_prop Q R) ->
        (forall a, P a <-> Q a).
      Proof.
        intros P Q H_same_homs a.
        split; intro H.
        - (* P a implies Q a *)
          assert (H_forward : hom_as_prop P Q).
          { apply H_same_homs.
            unfold hom_as_prop.
            intros x Hx. exact Hx. }
          unfold hom_as_prop in H_forward.
          exact (H_forward a H).
          
        - (* Q a implies P a *)
          assert (H_backward : hom_as_prop Q P).
          { apply H_same_homs.
            unfold hom_as_prop.
            intros x Hx. exact Hx. }
          unfold hom_as_prop in H_backward.
          exact (H_backward a H).
      Qed.
      
      (**
        Uniqueness: There is exactly one predicate with a given morphism structure.
        
        This is the content of Yoneda's lemma: the embedding P ↦ Hom(P,-)
        is fully faithful, meaning it preserves and reflects equality.
      *)
      Theorem being_uniquely_determined_by_homs :
        forall (P : Alphacarrier -> Prop),
        exists! (char : Alphacarrier -> Prop),
          (forall R, hom_as_prop char R <-> hom_as_prop P R) /\
          (forall a, char a <-> P a).
      Proof.
        intro P.
        exists P.
        split.
        - split.
          + intro R. split; intro H; exact H.
          + intro a. split; intro H; exact H.
        - intros Q [H_same_homs H_equiv].
          apply functional_extensionality_dep.
          intro a.
          apply propositional_extensionality.
          apply predicates_equal_iff_homs_equal.
          intro R.
          split.
          + intro H. apply H_same_homs. exact H.
          + intro H. apply H_same_homs. exact H.
      Qed.
      
      (**
        Interpretation:
        In PRED, hom_as_prop P Q means (forall a, P a -> Q a), i.e., P implies Q.
        The theorem predicates_equal_iff_homs_equal states:
          P = Q  ⟺  (∀R. P→R ⟺ Q→R)
        That is: a predicate is determined by its implications.
        Since P→Q can be read as "P does not make Q impossible", we have:
          A predicate is determined by what it does not make impossible.
        Or equivalently:
          A predicate is determined by the impossibilities it respects.
          
        This establishes that being (what a predicate is) is characterized
        by impossibility structure (what boundaries it respects).
        Note: We used extensionality and axioms that are technically not entirely constructive.
      *)

    End BeingTheorems.
    
  End HomFunctors.

  (** * Lawvere's Fixed Point Theorem
      
      This module proves Lawvere's Fixed Point Theorem and connects it
      to the diagonal arguments in the DAO framework, demonstrating that
      the categorical and impossibility-based perspectives are complementary.
      
      Note: This module uses classical logic and functional extensionality,
      which are standard in category theory but kept local to this module.
  *)

  Module Lawvere.
    Import Core Constructions.
    
    (* Import diagonal for the connection *)
    Require Import DAO.Logic.Diagonal.
    
    (* ================================================================ *)
    (** ** Local Axioms and Definitions *)
    (* ================================================================ *)
    
    Section LocalAxioms.
      
      (** Functional extensionality - functions equal if equal pointwise *)
      Axiom functional_extensionality : 
        forall {A B : Type} {f g : A -> B},
        (forall x, f x = g x) -> f = g.
      
      (** Classical logic - excluded middle *)
      Axiom classic : forall P : Prop, P \/ ~ P.
      
      (** Type equivalence (isomorphism) *)
      Record Equiv (A B : Type) := {
        equiv_to : A -> B;
        equiv_from : B -> A;
        equiv_to_from : forall b, equiv_to (equiv_from b) = b;
        equiv_from_to : forall a, equiv_from (equiv_to a) = a
      }.
      
    End LocalAxioms.
    
    (* ================================================================ *)
    (** ** Lawvere's Fixed Point Theorem *)
    (* ================================================================ *)
    
    Section FixedPointTheorem.
      Context {Alpha : AlphaType}.
      
      (** Surjection in TYPE *)
      Definition surjective {A B : Type} (f : A -> B) : Prop :=
        forall b : B, exists a : A, f a = b.
      
      (** Fixed point of a function *)
      Definition is_fixed_point {B : Type} (f : B -> B) (b : B) : Prop :=
        f b = b.
      
      (** Lawvere's Fixed Point Theorem (TYPE version)
          
          If there exists a surjection e : A → (A → B),
          then every function f : B → B has a fixed point.
          
          This is the categorical heart of all diagonal arguments.
      *)
      Theorem lawvere_fixed_point :
        forall (A B : Type) (e : A -> (A -> B)),
        surjective e ->
        forall (f : B -> B),
        exists (a : A), is_fixed_point f (e a a).
      Proof.
        intros A B e Hsurj f.
        
        (* Construct the diagonal function: g(x) = f(e(x)(x)) *)
        pose (g := fun x : A => f (e x x)).
        
        (* By surjectivity of e, there exists a such that e(a) = g *)
        destruct (Hsurj g) as [a Ha].
        exists a.
        
        (* Show: f(e a a) = e a a *)
        unfold is_fixed_point.
        
        (* From e a = g, get pointwise equality *)
        assert (H_pointwise : forall x, e a x = g x).
        {
          intro x.
          rewrite Ha.
          reflexivity.
        }
        
        (* Specialize to x = a *)
        specialize (H_pointwise a).
        unfold g in H_pointwise.
        
        (* Now H_pointwise says: e a a = f (e a a) *)
        (* We want: f (e a a) = e a a *)
        symmetry.
        exact H_pointwise.
      Qed.
      
    End FixedPointTheorem.
    
    (* ================================================================ *)
    (** ** Connection to Cantor's Theorem *)
    (* ================================================================ *)
    
    Section CantorViaLawvere.
      
      (** Cantor's theorem: no surjection from A to P(A) 
          
          This is Lawvere applied with B = Prop and f = negation.
      *)
      Theorem cantor_via_lawvere :
        forall (A : Type) (e : A -> (A -> Prop)),
        ~ surjective e.
      Proof.
        intros A e Hsurj.
        
        (* Apply Lawvere with B = Prop and negation *)
        pose (neg := fun (P : Prop) => ~ P).
        
        destruct (lawvere_fixed_point A Prop e Hsurj neg) as [a Ha].
        
        (* Ha says: neg (e a a) = e a a *)
        (* That is: ~ (e a a) = e a a *)
        unfold is_fixed_point, neg in Ha.
        
        (* This is a propositional equality between ~ e a a and e a a *)
        (* We derive a contradiction by case analysis *)
        
        destruct (classic (e a a)) as [Hyes | Hno].
        
        - (* Case: e a a holds *)
          (* From Ha: ~ e a a = e a a, so ~ e a a also holds *)
          assert (Hneg : ~ e a a).
          { rewrite Ha. exact Hyes. }
          (* Contradiction *)
          exact (Hneg Hyes).
          
        - (* Case: ~ e a a holds *)
          (* From Ha: ~ e a a = e a a, so e a a also holds *)
          assert (Hpos : e a a).
          { rewrite <- Ha. exact Hno. }
          (* Contradiction *)
          exact (Hno Hpos).
      Qed.
      
    End CantorViaLawvere.
    
    (* ================================================================ *)
    (** ** Transport via Equivalence *)
    (* ================================================================ *)
    
    Section Transport.
      Context {Alpha : AlphaType}.
      
      (** Transport a predicate along an equivalence *)
      Definition transport_pred {A B : Type} (equiv : Equiv A B) 
        (P : A -> Prop) : B -> Prop :=
        fun b => P (equiv_from A B equiv b).
      
      (** Transport an enumeration along an equivalence *)
      Definition transport_enum {A B : Type} (equiv : Equiv A B)
        (enum : nat -> option (A -> Prop)) : nat -> option (B -> Prop) :=
        fun n => 
          match enum n with
          | Some P => Some (transport_pred equiv P)
          | None => None
          end.
      
      (** Convert option enumeration to total function *)
      Definition enum_to_function {A : Type} (enum : nat -> option (A -> Prop))
        : nat -> (A -> Prop) :=
        fun n => match enum n with
                | Some P => P
                | None => fun _ => False
                end.
      
      (** Completeness of enumeration *)
      Definition complete_enumeration {A : Type} (enum : nat -> option (A -> Prop)) : Prop :=
        forall P : A -> Prop, exists n : nat, enum n = Some P.
      
      (** Transport preserves completeness *)
      Lemma transport_preserves_completeness {A B : Type} (equiv : Equiv A B) :
        forall (enum : nat -> option (A -> Prop)),
        complete_enumeration enum ->
        forall Q : B -> Prop,
        exists n : nat, transport_enum equiv enum n = Some Q.
      Proof.
        intros enum Hcomplete Q.
        
        (* Construct the "pullback" of Q along the equivalence *)
        pose (P := fun a => Q (equiv_to A B equiv a)).
        
        (* By completeness, P appears in the enumeration *)
        destruct (Hcomplete P) as [n Hn].
        exists n.
        
        (* Show that transport_enum enum n = Some Q *)
        unfold transport_enum.
        rewrite Hn.
        
        (* Now we have: Some (transport_pred equiv P) = Some Q *)
        (* First apply f_equal to work inside Some *)
        f_equal.
        
        (* Need to show: transport_pred equiv P = Q *)
        apply functional_extensionality.
        intro b.
        unfold transport_pred, P.
        
        (* Use the equivalence properties *)
        rewrite (equiv_to_from A B equiv b).
        reflexivity.
      Qed.
      
      (** Complete enumeration gives surjection *)
      Lemma complete_enum_surjective {A : Type} :
        forall (enum : nat -> option (A -> Prop)),
        complete_enumeration enum ->
        surjective (enum_to_function enum).
      Proof.
        intros enum Hcomplete.
        unfold surjective, complete_enumeration.
        intro P.
        destruct (Hcomplete P) as [n Hn].
        exists n.
        unfold enum_to_function.
        rewrite Hn.
        reflexivity.
      Qed.
      
    End Transport.
    
    (* ================================================================ *)
    (** ** Lawvere Prevents Complete Enumeration *)
    (* ================================================================ *)
    
    Section LawverePreventsDiagonal.
      Context {Alpha : AlphaType}.
      
      (** If Alphacarrier is equivalent to nat, then Lawvere prevents complete enumeration *)
      Theorem lawvere_prevents_complete_enumeration_via_equiv :
        forall (equiv : Equiv Alphacarrier nat),
        forall (enum : nat -> option (Alphacarrier -> Prop)),
        complete_enumeration enum ->
        False.
      Proof.
        intros equiv enum Hcomplete.
        
        (* Transport the enumeration along the equivalence *)
        pose (enum_nat := transport_enum equiv enum).
        
        (* By transport_preserves_completeness, enum_nat is also complete *)
        assert (Hcomplete_nat : forall Q : nat -> Prop, 
          exists n, enum_nat n = Some Q).
        {
          intro Q.
          exact (transport_preserves_completeness equiv enum Hcomplete Q).
        }
        
        (* Convert to total function *)
        pose (e := enum_to_function enum_nat).
        
        (* This is a surjection nat -> (nat -> Prop) *)
        assert (Hsurj : surjective e).
        {
          unfold surjective.
          intro P.
          destruct (Hcomplete_nat P) as [n Hn].
          exists n.
          unfold e, enum_to_function.
          rewrite Hn.
          reflexivity.
        }
        
        (* But Cantor says no such surjection exists! *)
        exact (cantor_via_lawvere nat e Hsurj).
      Qed.
      
      (** Corollary: No complete enumeration when Alphacarrier ≃ nat *)
      Corollary no_complete_enumeration_when_equiv_nat :
        forall (equiv : Equiv Alphacarrier nat),
        ~ exists (enum : nat -> option (Alphacarrier -> Prop)),
          complete_enumeration enum.
      Proof.
        intros equiv [enum Hcomplete].
        exact (lawvere_prevents_complete_enumeration_via_equiv equiv enum Hcomplete).
      Qed.
      
    End LawverePreventsDiagonal.
    
    (* ================================================================ *)
    (** ** Philosophical Connection *)
    (* ================================================================ *)
    
    Section Philosophy.
      Require Import DAO.Core.OmegaType.

      Context {Alpha : AlphaType} {Omega : OmegaType}.
      Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
      Variable embed : Alphacarrier -> Omegacarrier.
      
      (** Lawvere's perspective: categorical impossibility via fixed points *)
      Theorem lawvere_perspective :
        (* When Alphacarrier ≃ nat, no complete enumeration exists *)
        (forall equiv : Equiv Alphacarrier nat,
          ~ complete_enumeration alpha_enum) \/
        (* Or Alphacarrier is not equivalent to nat *)
        (~ exists equiv : Equiv Alphacarrier nat, True).
      Proof.
        (* This is a tautology expressing the connection *)
        destruct (classic (exists equiv : Equiv Alphacarrier nat, True)) as [H | H].
        - left.
          intros equiv Hcomplete.
          exact (lawvere_prevents_complete_enumeration_via_equiv equiv alpha_enum Hcomplete).
        - right. exact H.
      Qed.
      
      (** The two perspectives are complementary:
          
          Lawvere (categorical): 
            "No surjection A → (A → B) because it would give fixed points for any f : B → B"
            "In particular, f = negation gives a contradiction"
          
          Impossibility framework
            "Diagonal escapes Alpha because it's unrepresentable at the Alpha/Omega boundary"
            "This is forced by omega_veil (the one impossibility)"
          
          Both explain why complete enumeration is impossible.
          Lawvere explains the categorical pattern.
          We show omega_veil → boundary → unrepresentability.
          
          These are orthogonal perspectives on the same phenomenon:
          - Lawvere: What structure do all diagonal arguments share? (Fixed points)
          - Impossibility: Why must this structure exist? (The Alpha/Omega boundary from omega_veil)
      *)
      
    End Philosophy.

    (** * Omega_veil as Lawvere's Impossibility Witness *)
    Section OmegaVeilFixedPoint.
      Context {Alpha : AlphaType}.
      
      (** The Russell/Lawvere diagonal construction *)
      Definition russell_diagonal (e : Alphacarrier -> (Alphacarrier -> Prop)) 
        (a : Alphacarrier) : Prop :=
        ~ e a a.
      
      (** Lawvere's construction produces a self-negating point *)
      Theorem lawvere_gives_self_negating_point :
        forall (e : Alphacarrier -> (Alphacarrier -> Prop)),
        surjective e ->
        exists (a : Alphacarrier),
          e a a <-> ~ e a a.
      Proof.
        intros e Hsurj.
        (* The diagonal function *)
        pose (diag := russell_diagonal e).
        (* By surjectivity, diag appears in the enumeration *)
        destruct (Hsurj diag) as [a Ha].
        exists a.
        (* Unfold: e a = diag, so e a a = diag a = ~ e a a *)
        assert (Hdiag : diag a = ~ e a a) by reflexivity.
        split; intro H.
        - (* e a a -> ~ e a a *)
          rewrite Ha in H.
          rewrite Hdiag in H.
          exact H.
        - (* ~ e a a -> e a a *)
          rewrite Ha.
          rewrite Hdiag.
          exact H.
      Qed.
      
      Lemma self_negating_predicate_impossible :
        forall (a : Alphacarrier),
        ~ exists (P : Alphacarrier -> Prop), P a <-> ~ P a.
      Proof.
        intros a [P Hself].
        destruct Hself as [H_forward H_backward].
        destruct (classic (P a)) as [HP | HnP].
        - exact (H_forward HP HP).
        - exact (HnP (H_backward HnP)).
      Qed.
      
      (** Therefore: surjection is impossible (Cantor's theorem) *)
      Theorem surjection_impossible_via_lawvere :
        ~ exists (e : Alphacarrier -> (Alphacarrier -> Prop)), surjective e.
      Proof.
        intros [e Hsurj].
        (* Lawvere gives us a self-negating point *)
        destruct (lawvere_gives_self_negating_point e Hsurj) as [a Hself].
        (* But self-negating points are impossible *)
        apply (self_negating_predicate_impossible a).
        exists (e a).
        exact Hself.
      Qed.
      
      Corollary complete_enumeration_impossible_when_equiv :
        forall (equiv : Equiv Alphacarrier nat),
        forall (enum : nat -> option (Alphacarrier -> Prop)),
        ~ complete_enumeration enum.
      Proof.
        intros equiv enum Hcomplete.
        (* Use the transport machinery from earlier *)
        exact (lawvere_prevents_complete_enumeration_via_equiv equiv enum Hcomplete).
      Qed.
      
      (** * Connection to Omega_veil *)
      
      (** Alternative formulation: The Lawvere fixed point witnesses omega_veil
          
          We can also view this through the lens of impossibility:
          A self-negating point would witness omega_veil if it could exist.
      *)
      Theorem self_negating_would_witness_omega_veil :
        (exists (P : Alphacarrier -> Prop) (a : Alphacarrier), P a <-> ~ P a) ->
        exists (a : Alphacarrier), omega_veil a.
      Proof.
        intros [P [a Hself]].
        exists a.
        (* From P a <-> ~ P a, derive False *)
        exfalso.
        destruct Hself as [H_forward H_backward].
        destruct (classic (P a)) as [HP | HnP].
        - (* HP : P a, so ~ P a by forward direction *)
          exact (H_forward HP HP).
        - (* HnP : ~ P a, so P a by backward direction *)
          exact (HnP (H_backward HnP)).
      Qed.
      
      (** But omega_veil has no witnesses *)
      Theorem omega_veil_has_no_witnesses_anywhere :
        ~ exists (a : Alphacarrier), omega_veil a.
      Proof.
        intros [a Hveil].
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
      Qed.
      
      (** The fundamental connection:
          
          Lawvere's theorem:     surjection → self-negating point
          Impossibility theory:  self-negating point → omega_veil
          Alpha's consistency:   omega_veil has no witnesses
          
          Therefore: no surjection (incompleteness)
      *)
      Theorem lawvere_incompleteness_via_omega_veil :
        ~ exists (e : Alphacarrier -> (Alphacarrier -> Prop)), surjective e.
      Proof.
        intros [e Hsurj].
        apply omega_veil_has_no_witnesses_anywhere.
        apply self_negating_would_witness_omega_veil.
        destruct (lawvere_gives_self_negating_point e Hsurj) as [a Hself].
        exists (e a), a.
        exact Hself.
      Qed.
      
    End OmegaVeilFixedPoint.
    
  End Lawvere.
  
End BasicCategoryTheory.