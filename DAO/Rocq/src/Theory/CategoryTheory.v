(** * Basic Category Theory in AlphaType
    
    This module develops the fundamental concepts of category theory
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
      
      Definition postcomposition_functor (H : Functor C D) :
        Functor (FunctorCategory D E) (FunctorCategory C E).
      Proof.
        refine ({|
          F_obj := fun G => functor_compose G H;
          F_hom := fun G K beta => 
            {| components := fun X => components beta (F_obj H X);
              naturality := _ |}
        |}).
        - (* Naturality *)
          intros X Y f. simpl.
          apply naturality.
        - (* Preserves identity *)
          intro G.
          apply nattrans_ext.
          intro X. reflexivity.
        - (* Preserves composition *)
          intros G K L beta alpha.
          apply nattrans_ext.
          intro X. reflexivity.
      Defined.
      
    End FunctorCategoryProperties.
    
    (** Special case: endofunctor categories *)
    Definition EndofunctorCategory (C : Category) := FunctorCategory C C.
    
    (** Example: In TYPE, endofunctors include many familiar constructions *)
    Section Examples.
      Context {Alpha : AlphaType}.
      
      (** The endofunctor category of TYPE contains functors like List, Option, etc. *)
      Definition TYPE_endofunctors := EndofunctorCategory TYPE.
      
      (** The endofunctor category of PRED is particularly interesting for AlphaType *)
      Definition PRED_endofunctors := EndofunctorCategory PRED.
      
      (* Note: In PRED_endofunctors, we might discover functors that preserve
        or reflect impossibility in interesting ways. This could connect to
        the omega_veil structure, but we haven't explored this yet. *)
      
    End Examples.
    
  End FunctorCategories.
  
End BasicCategoryTheory.