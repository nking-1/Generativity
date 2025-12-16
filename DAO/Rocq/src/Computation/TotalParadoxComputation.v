(** * TotalParadoxComputation.v
    
    Totality of Paradox Computation: Why omega_veil enables total functions.
    
    Core Insight:
    Traditional computation fails on paradoxes because there's nowhere for
    contradictions to go. In DAO, omega_veil is a universal sink - every
    computation either produces consistent output or drains. There's no
    third option (stuck/loop/crash).
    
    This gives us:
    1. Total functions over paradox-containing domains
    2. A foundation for a total programming language
    3. A model where "undefined" is just another value (the drained one)
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import DAO.Theory.CategoryTheory.
Require Import DAO.Computation.ParadoxAutomaton.

Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import PeanoNat.
Require Import Lia.

(* Import some stronger axioms *)
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.ProofIrrelevance.

Module TotalParadoxComputation.

  Import ImpossibilityAlgebra.Core.
  Import ParadoxAutomaton.

  (* ================================================================ *)
  (** ** Part I: The Universal Sink Property *)
  (* ================================================================ *)
  
  Section UniversalSink.
    Context {Alpha : AlphaType}.
    
    (** omega_veil is the universal sink: every impossible predicate
        has a canonical morphism to it *)
    
    Definition sink_morphism (P : Alphacarrier -> Prop) 
      (H : Is_Impossible P) : forall a, P a -> omega_veil a.
    Proof.
      intros a HPa.
      apply H.
      exact HPa.
    Defined.
    
    (** The sink is universal: it's the unique target for impossible predicates *)
    Theorem sink_uniqueness :
      forall (P : Alphacarrier -> Prop) (H : Is_Impossible P),
      forall (Q : Alphacarrier -> Prop),
      (forall a, P a -> Q a) ->
      Is_Impossible Q ->
      forall a, Q a <-> omega_veil a.
    Proof.
      intros P HP Q Hmorph HQ a.
      apply HQ.
    Qed.
    
    (** omega_veil absorbs: composing with omega_veil gives omega_veil *)
    Theorem sink_absorbs :
      forall (P : Alphacarrier -> Prop),
      Is_Impossible (fun a => P a /\ omega_veil a).
    Proof.
      intros P a.
      split.
      - intros [_ Hveil]. exact Hveil.
      - intro Hveil. 
        exfalso. 
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.
    
    (** omega_veil is idempotent: draining twice = draining once *)
    Theorem sink_idempotent :
      forall a, omega_veil a <-> (omega_veil a /\ omega_veil a).
    Proof.
      intro a.
      split.
      - intro H. split; exact H.
      - intros [H _]. exact H.
    Qed.
    
  End UniversalSink.

  (* ================================================================ *)
  (** ** Part II: Computation Results - A Proper Sum Type *)
  (* ================================================================ *)
  
  Section ComputationResults.
    Context {Alpha : AlphaType}.
    
    (** Every computation produces exactly one of two results *)
    Inductive CompResult (A : Type) : Type :=
      | Computed : A -> CompResult A          (* Successful computation *)
      | Drained : CompResult A.               (* Drained to omega_veil *)
    
    Arguments Computed {A} _.
    Arguments Drained {A}.
    
    (** CompResult is a monad *)
    Definition comp_return {A : Type} (x : A) : CompResult A :=
      Computed x.
    
    Definition comp_bind {A B : Type} 
      (m : CompResult A) (f : A -> CompResult B) : CompResult B :=
      match m with
      | Computed a => f a
      | Drained => Drained
      end.
    
    (** Monad laws *)
    Theorem comp_left_id : forall {A B : Type} (a : A) (f : A -> CompResult B),
      comp_bind (comp_return a) f = f a.
    Proof.
      intros. reflexivity.
    Qed.
    
    Theorem comp_right_id : forall {A : Type} (m : CompResult A),
      comp_bind m comp_return = m.
    Proof.
      intros A [a | ]; reflexivity.
    Qed.
    
    Theorem comp_assoc : forall {A B C : Type} 
      (m : CompResult A) (f : A -> CompResult B) (g : B -> CompResult C),
      comp_bind (comp_bind m f) g = comp_bind m (fun a => comp_bind (f a) g).
    Proof.
      intros A B C [a | ] f g; reflexivity.
    Qed.
    
    (** Drained is the zero element *)
    Theorem drained_absorbs_left : forall {A B : Type} (f : A -> CompResult B),
      comp_bind Drained f = Drained.
    Proof.
      intros. reflexivity.
    Qed.
    
    Theorem drained_absorbs_right : forall {A B : Type} (m : CompResult A),
      comp_bind m (fun _ => @Drained B) = Drained.
    Proof.
      intros A B [a | ]; reflexivity.
    Qed.
    
  End ComputationResults.

  (* ================================================================ *)
  (** ** Part III: Total Functions via Drainage *)
  (* ================================================================ *)
  
  Section TotalFunctions.
    Context {Alpha : AlphaType}.
    
    (** A paradox-aware function: always returns a result *)
    Definition TotalFun (A B : Type) : Type :=
      A -> CompResult B.
    
    (** Composition of total functions *)
    Definition total_compose {A B C : Type} 
      (g : TotalFun B C) (f : TotalFun A B) : TotalFun A C :=
      fun a => comp_bind (f a) g.
    
    (** Identity total function *)
    Definition total_id {A : Type} : TotalFun A A :=
      fun a => @Computed A a.
    
    (** Composition laws *)
    Theorem total_compose_assoc : forall {A B C D : Type}
      (h : TotalFun C D) (g : TotalFun B C) (f : TotalFun A B),
      total_compose h (total_compose g f) = 
      total_compose (total_compose h g) f.
    Proof.
      intros.
      unfold total_compose.
      extensionality a.
      destruct (f a); reflexivity.
    Qed.
    
    Theorem total_compose_id_left : forall {A B : Type} (f : TotalFun A B),
      total_compose total_id f = f.
    Proof.
      intros.
      unfold total_compose, total_id.
      extensionality a.
      destruct (f a); reflexivity.
    Qed.
    
    Theorem total_compose_id_right : forall {A B : Type} (f : TotalFun A B),
      total_compose f total_id = f.
    Proof.
      intros.
      unfold total_compose, total_id.
      extensionality a.
      reflexivity.
    Qed.
    
    (** The drain function - sends anything to Drained *)
    Definition drain {A B : Type} : TotalFun A B :=
      fun _ => @Drained B.
    
    (** Drain absorbs composition *)
    Theorem drain_absorbs_post : forall {A B C : Type} (f : TotalFun A B),
      total_compose (@drain B C) f = drain.
    Proof.
      intros.
      unfold total_compose, drain.
      extensionality a.
      destruct (f a); reflexivity.
    Qed.
    
    Theorem drain_absorbs_pre : forall {A B C : Type} (g : TotalFun B C),
      total_compose g (@drain A B) = drain.
    Proof.
      intros.
      unfold total_compose, drain.
      reflexivity.
    Qed.
    
  End TotalFunctions.

  (* ================================================================ *)
  (** ** Part IV: Lifting Partial Functions to Total Functions *)
  (* ================================================================ *)
  
  Section LiftingPartial.
    Context {Alpha : AlphaType}.
    
    (** A partial function is one that may be undefined *)
    Definition PartialFun (A B : Type) : Type :=
      A -> option B.
    
    (** Lift a partial function to a total one *)
    Definition lift_partial {A B : Type} (f : PartialFun A B) : TotalFun A B :=
      fun a => match f a with
               | Some b => @Computed B b
               | None => @Drained B    (* Undefined → Drained *)
               end.
    
    (** The key theorem: lifting makes everything total *)
    Theorem lifting_total : forall {A B : Type} (f : PartialFun A B) (a : A),
      exists r : CompResult B, lift_partial f a = r.
    Proof.
      intros A B f a.
      unfold lift_partial.
      destruct (f a).
      - exists (@Computed B b). reflexivity.
      - exists (@Drained B). reflexivity.
    Qed.
    
    (** Division as a partial function made total *)
    Definition partial_div (n m : nat) : option nat :=
      match m with
      | 0 => None       (* Undefined *)
      | S m' => Some (n / m)
      end.
    
    Definition total_div : TotalFun (nat * nat) nat :=
      fun '(n, m) => lift_partial (fun '(n, m) => partial_div n m) (n, m).
    
    (** Division by zero drains instead of crashing *)
    Theorem div_by_zero_drains : forall n,
      total_div (n, 0) = @Drained nat.
    Proof.
      intro n.
      unfold total_div, lift_partial, partial_div.
      reflexivity.
    Qed.
    
    (** Division by non-zero computes *)
    Theorem div_by_nonzero_computes : forall n m,
      m > 0 ->
      exists q, total_div (n, m) = @Computed nat q.
    Proof.
      intros n m Hpos.
      unfold total_div, lift_partial, partial_div.
      destruct m.
      - lia.
      - exists (n / S m). reflexivity.
    Qed.
    
  End LiftingPartial.

  (* ================================================================ *)
  (** ** Part V: The Automaton is Total *)
  (* ================================================================ *)
  
  Section AutomatonTotality.
    Context {Alpha : AlphaType}.
    
    (** Every symbol has a defined drainage result *)
    Theorem drain_simple_total : forall (s : ParadoxSymbol),
      exists r : DrainageResult (Alpha := Alpha), 
      drain_simple s = r.
    Proof.
      intro s.
      destruct s; simpl; eauto.
    Qed.
    
    (** Every transition is defined *)
    Theorem transition_total : forall (st : AutomatonState) (sym : ParadoxSymbol),
      exists (st' : AutomatonState) (r : DrainageResult (Alpha := Alpha)),
      transition st sym = (st', r).
    Proof.
      intros st sym.
      unfold transition.
      destruct st; destruct (drain_simple sym) eqn:Hdrain; eauto.
    Qed.
    
    (** Stepping the automaton is total *)
    Theorem step_fa_total : forall (fa : ParadoxFA) (sym : ParadoxSymbol),
      exists fa' : ParadoxFA, step_fa fa sym = fa'.
    Proof.
      intros fa sym.
      unfold step_fa.
      destruct (transition (fa_state fa) sym) as [st' r].
      eauto.
    Qed.
    
    (** Running the automaton is total *)
    Theorem run_fa_total : forall (fa : ParadoxFA) (input : list ParadoxSymbol),
      exists fa' : ParadoxFA, run_fa fa input = fa'.
    Proof.
      intros fa input.
      generalize dependent fa.
      induction input as [| sym rest IH]; intro fa.
      - (* Empty input *)
        exists fa. reflexivity.
      - (* sym :: rest *)
        simpl.
        destruct (step_fa_total fa sym) as [fa' Hstep].
        rewrite Hstep.
        apply IH.
    Qed.
    
    (** The main totality theorem *)
    Theorem automaton_total : forall (input : list ParadoxSymbol),
      exists fa : ParadoxFA, process (Alpha := Alpha) input = fa.
    Proof.
      intro input.
      unfold process.
      apply run_fa_total.
    Qed.
    
    (** Strong form: we can compute the result *)
    Definition process_computable (input : list ParadoxSymbol) 
      : { fa : ParadoxFA | process (Alpha := Alpha) input = fa }.
    Proof.
      exists (process input).
      reflexivity.
    Defined.
    
  End AutomatonTotality.

  (* ================================================================ *)
  (** ** Part VI: Reversible Fragment *)
  (* ================================================================ *)
  
  Section ReversibleComputation.
    Context {Alpha : AlphaType}.
    
    (** A reversible total function has an inverse *)
    Record ReversibleFun (A B : Type) := {
      forward : TotalFun A B;
      backward : TotalFun B A;
      
      (* Round-trip laws - but only for Computed values *)
      forward_backward : forall b,
        comp_bind (backward b) forward = @Computed B b \/
        comp_bind (backward b) forward = @Drained B;
      backward_forward : forall a,
        comp_bind (forward a) backward = @Computed A a \/
        comp_bind (forward a) backward = @Drained A
    }.
    
    Arguments forward {A B} _.
    Arguments backward {A B} _.
    
    (** Strict reversibility: round-trip always succeeds *)
    Record StrictReversibleFun (A B : Type) := {
      s_forward : A -> B;
      s_backward : B -> A;
      s_forward_backward : forall b, s_forward (s_backward b) = b;
      s_backward_forward : forall a, s_backward (s_forward a) = a
    }.
    
    (** Lift strict reversible to reversible *)
    Definition lift_strict {A B : Type} (f : StrictReversibleFun A B) 
      : ReversibleFun A B.
    Proof.
      refine ({|
        forward := fun a => @Computed B (@s_forward A B f a);
        backward := fun b => @Computed A (@s_backward A B f b)
      |}).
      - intro b. left. simpl. f_equal. apply (@s_forward_backward A B f).
      - intro a. left. simpl. f_equal. apply (@s_backward_forward A B f).
    Defined.
    
    (** Reversible functions preserve "computedness" *)
    Theorem reversible_preserves_computed : forall {A B : Type} 
      (f : StrictReversibleFun A B) (a : A),
      exists b, forward (lift_strict f) a = @Computed B b.
    Proof.
      intros A B f a.
      exists (@s_forward A B f a).
      reflexivity.
    Qed.
    
    (** Reversible functions don't drain *)
    Theorem strict_reversible_no_drain : forall {A B : Type}
      (f : StrictReversibleFun A B) (a : A),
      forward (lift_strict f) a <> @Drained B.
    Proof.
      intros A B f a.
      simpl.
      discriminate.
    Qed.

    Definition rev_id {A : Type} : StrictReversibleFun A A := {|
      s_forward := fun a => a;
      s_backward := fun a => a;
      s_forward_backward := fun _ => eq_refl;
      s_backward_forward := fun _ => eq_refl
    |}.

    Definition rev_compose {A B C : Type}
      (g : StrictReversibleFun B C) (f : StrictReversibleFun A B) 
      : StrictReversibleFun A C.
    Proof.
      refine ({|
        s_forward := fun a => @s_forward B C g (@s_forward A B f a);
        s_backward := fun c => @s_backward A B f (@s_backward B C g c)
      |}).
      - intro c. 
        rewrite (@s_forward_backward A B f).  (* Now: s_forward B C g (s_backward B C g c) = c *)
        apply (@s_forward_backward B C g).
      - intro a. 
        rewrite (@s_backward_forward B C g).  (* Now: s_backward A B f (s_forward A B f a) = a *)
        apply (@s_backward_forward A B f).
    Defined.

    Definition rev_inverse {A B : Type} (f : StrictReversibleFun A B) 
      : StrictReversibleFun B A := {|
      s_forward := @s_backward A B f;
      s_backward := @s_forward A B f;
      s_forward_backward := @s_backward_forward A B f;
      s_backward_forward := @s_forward_backward A B f
    |}.

    Theorem rev_inverse_left : forall {A B : Type} (f : StrictReversibleFun A B),
      forall a, @s_forward A A (rev_compose (rev_inverse f) f) a = a.
    Proof.
      intros A B f a.
      simpl.
      apply (@s_backward_forward A B f).
    Qed.

    Theorem rev_inverse_right : forall {A B : Type} (f : StrictReversibleFun A B),
      forall b, @s_forward B B (rev_compose f (rev_inverse f)) b = b.
    Proof.
      intros A B f b.
      simpl.
      apply (@s_forward_backward A B f).
    Qed.
    
  End ReversibleComputation.

  (* ================================================================ *)
  (** ** Part VII: Connection to Entropy *)
  (* ================================================================ *)
  
  Section EntropyConnection.
    Context {Alpha : AlphaType}.
    
    (** Reversible computations have zero entropy change *)
    Definition entropy_change {A B : Type} (f : TotalFun A B) (a : A) : nat :=
      match f a with
      | Computed _ b => 0
      | Drained _ => 1
      end.
    
    (** Strict reversible functions never increase entropy *)
    Theorem strict_reversible_zero_entropy : forall {A B : Type}
      (f : StrictReversibleFun A B) (a : A),
      entropy_change (@forward A B (lift_strict f)) a = 0.
    Proof.
      intros A B f a.
      unfold entropy_change, lift_strict.
      simpl.
      reflexivity.
    Qed.
    
    (** The drain function always increases entropy *)
    Theorem drain_increases_entropy : forall {A B : Type} (a : A),
      entropy_change (@drain A B) a = 1.
    Proof.
      intros.
      reflexivity.
    Qed.
    
    (** Composition with drain always increases entropy *)
    Theorem compose_drain_entropy : forall {A B C : Type} 
      (f : TotalFun A B) (a : A),
      entropy_change (total_compose (@drain B C) f) a >= 
      entropy_change f a.
    Proof.
      intros A B C f a.
      unfold total_compose, entropy_change, drain.
      destruct (f a); simpl; lia.
    Qed.
    
  End EntropyConnection.

  (* ================================================================ *)
  (** ** Part VIII: The Category of Total Paradox Computations *)
  (* ================================================================ *)
  
  (* ================================================================ *)
  (** ** Part VIII: The Category of Total Paradox Computations *)
  (* ================================================================ *)
  
  Section CategoryStructure.
    Context {Alpha : AlphaType}.
    
    Import BasicCategoryTheory.Core.
    
    (* -------------------------------------------------------------- *)
    (** *** The Category TOTAL *)
    (* -------------------------------------------------------------- *)
    
    (** Objects: Types
        Morphisms: Total functions (always return Computed or Drained)
        
        This is the category where paradoxes are first-class:
        instead of undefined behavior, we get Drained. *)
    
    Definition TOTAL : Category.
    Proof.
      refine ({|
        Obj := Type;
        Hom := TotalFun;
        id := @total_id;
        compose := @total_compose
      |}).
      - intros. apply total_compose_assoc.
      - intros. apply total_compose_id_left.
      - intros. apply total_compose_id_right.
    Defined.
    
    (* -------------------------------------------------------------- *)
    (** *** Zero Morphisms: The Categorical View of Drainage *)
    (* -------------------------------------------------------------- *)
    
    (** In TOTAL, drain acts as a zero morphism:
        - Composing with drain on either side gives drain
        - This is the categorical manifestation of omega_veil absorption *)
    
    Theorem drain_is_zero_left : forall (A B C : Type) (f : TotalFun A B),
      total_compose (@drain B C) f = @drain A C.
    Proof.
      intros.
      apply drain_absorbs_post.
    Qed.
    
    Theorem drain_is_zero_right : forall (A B C : Type) (g : TotalFun B C),
      total_compose g (@drain A B) = @drain A C.
    Proof.
      intros.
      apply drain_absorbs_pre.
    Qed.
    
    Theorem drain_compose_drain : forall (A B C : Type),
      total_compose (@drain B C) (@drain A B) = @drain A C.
    Proof.
      intros.
      apply drain_is_zero_left.
    Qed.
    
    (** Zero morphisms are unique: any morphism that absorbs is drain *)
    Theorem zero_unique : forall {A B : Type} (z : TotalFun A B),
      (forall C (f : TotalFun B C), total_compose f z = @drain A C) ->
      forall a, z a = @Drained B.
    Proof.
      intros A B z Habsorbs a.
      (* Apply Habsorbs with f = total_id *)
      specialize (Habsorbs B total_id).
      unfold total_compose, total_id, drain in Habsorbs.
      (* Now Habsorbs : (fun a => match z a with ... end) = (fun _ => Drained) *)
      apply (f_equal (fun f => f a)) in Habsorbs.
      destruct (z a) as [b | ].
      - simpl in Habsorbs. discriminate.
      - reflexivity.
    Qed.
    
    (* -------------------------------------------------------------- *)
    (** *** The Groupoid REV of Reversible Computations *)
    (* -------------------------------------------------------------- *)
    
    (** The reversible fragment forms a groupoid:
        - Every morphism has an inverse
        - No drainage occurs
        - This is the "conservative" part of computation *)
    
    Definition REV : Category.
    Proof.
      refine ({|
        Obj := Type;
        Hom := StrictReversibleFun;
        id := @rev_id;
        compose := fun A B C g f => @rev_compose A B C g f
      |}).
      - (* associativity *)
        intros W X Y Z h g f.
        unfold rev_compose.
        f_equal; apply proof_irrelevance.
      - (* left identity *)
        intros X Y f.
        unfold rev_compose, rev_id.
        destruct f.
        simpl.
        f_equal; apply proof_irrelevance.
      - (* right identity *)
        intros X Y f.
        unfold rev_compose, rev_id.
        destruct f.
        simpl.
        f_equal; apply proof_irrelevance.
    Defined.
    
    (** Helper: two StrictReversibleFun are equal if their components are *)
    Lemma strict_rev_eq : forall {A B : Type} (f g : StrictReversibleFun A B),
      @s_forward A B f = @s_forward A B g ->
      @s_backward A B f = @s_backward A B g ->
      f = g.
    Proof.
      intros A B [f_fwd f_bwd f_fb f_bf] [g_fwd g_bwd g_fb g_bf] Hfwd Hbwd.
      simpl in *.
      subst.
      f_equal; apply proof_irrelevance.
    Qed.
    
    (** Every morphism in REV is invertible *)
    Theorem rev_is_groupoid : forall {A B : Type} (f : Hom REV A B),
      exists (g : Hom REV B A),
        compose REV g f = id REV A /\
        compose REV f g = id REV B.
    Proof.
      intros A B f.
      exists (rev_inverse f).
      destruct f as [fwd bwd fwd_bwd bwd_fwd].
      split.
      - (* g ∘ f = id A *)
        apply strict_rev_eq.
        + simpl. extensionality a. apply bwd_fwd.
        + simpl. extensionality a. apply bwd_fwd.
      - (* f ∘ g = id B *)
        apply strict_rev_eq.
        + simpl. extensionality b. apply fwd_bwd.
        + simpl. extensionality b. apply fwd_bwd.
    Qed.
    
    (* -------------------------------------------------------------- *)
    (** *** The Inclusion Functor: REV → TOTAL *)
    (* -------------------------------------------------------------- *)
    
    (** Reversible computations embed into total computations *)
    
    Import BasicCategoryTheory.Functors.
    
    Definition rev_to_total_obj (A : Type) : Type := A.
    
    Definition rev_to_total_hom {A B : Type} 
      (f : StrictReversibleFun A B) : TotalFun A B :=
      @forward A B (lift_strict f).
    
    Definition IncludeREV : Functor REV TOTAL.
    Proof.
      refine ({|
        F_obj := fun (A : Obj REV) => A : Obj TOTAL;
        F_hom := fun (A B : Obj REV) (f : Hom REV A B) => 
                 @forward A B (lift_strict f) : Hom TOTAL A B
      |}).
      - (* Preserves identity *)
        intro A.
        unfold id, REV, TOTAL, total_id.
        simpl.
        extensionality a.
        reflexivity.
      - (* Preserves composition *)
        intros A B C g f.
        unfold compose, REV, TOTAL, total_compose.
        simpl.
        extensionality a.
        reflexivity.
    Defined.
    
    (** The inclusion is faithful: distinct reversible functions 
        give distinct total functions *)
    Theorem include_faithful : forall {A B : Type} 
      (f g : StrictReversibleFun A B),
      F_hom IncludeREV f = F_hom IncludeREV g ->
      forall a, @s_forward A B f a = @s_forward A B g a.
    Proof.
      intros A B f g Heq a.
      unfold F_hom, IncludeREV, rev_to_total_hom in Heq.
      apply (f_equal (fun h => h a)) in Heq.
      simpl in Heq.
      inversion Heq.
      reflexivity.
    Qed.
    
    (* -------------------------------------------------------------- *)
    (** *** The Entropy Functor: TOTAL → ℕ *)
    (* -------------------------------------------------------------- *)
    
    (** Entropy gives a functor to natural numbers (as a preorder category).
        This captures the thermodynamic structure categorically. *)
    
    (** We model ℕ as a thin category: Hom(m,n) is inhabited iff m ≤ n *)

    Open Scope nat_scope.
    
    Definition NAT_LE : Category.
    Proof.
      refine ({|
        Obj := nat;
        Hom := fun m n => m <= n;
        id := fun n => Nat.le_refl n;
        compose := fun m n p Hnp Hmn => Nat.le_trans m n p Hmn Hnp
      |}).
      - intros. apply proof_irrelevance.
      - intros. apply proof_irrelevance.
      - intros. apply proof_irrelevance.
    Defined.
    
    (** Note: A full entropy functor would require tracking entropy 
        across composition, which needs additional structure.
        For now, we note that:
        - Reversible morphisms map to id (zero entropy change)
        - drain maps to S (positive entropy change) *)
    
  End CategoryStructure.

End TotalParadoxComputation.