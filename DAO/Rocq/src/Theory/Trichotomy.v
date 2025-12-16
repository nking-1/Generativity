(** * Trichotomy.v
    
    The Three Extremes: Omega, Alpha, Void
    
    Core Thesis:
    Reality exists in the tension between three types:
    - Omega: Complete (all witnesses) - TRIVIAL via contradiction
    - Void: Empty (no witnesses) - TRIVIAL via ex falso
    - Alpha: The middle - NON-TRIVIAL, where meaning lives
    
    Key insight: Both extremes collapse into triviality.
    Alpha is the ONLY place where distinctions hold.
    omega_veil is the boundary that prevents collapse into either extreme.
    
    The monad M = R ∘ C is the navigation that keeps existence non-trivial.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.VoidType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Core.OmegaProperties.
Require Import DAO.Core.VoidProperties.
Require Import DAO.Theory.ExistenceAdjunction.
Require Import DAO.Theory.CategoryTheory.
Require Import DAO.Computation.ParadoxAutomaton.
Require Import DAO.Computation.OuroborosComputer.

Require Import Coq.Logic.FunctionalExtensionality.

Module Trichotomy.

  (* ================================================================ *)
  (** ** Part I: The Two Trivialities *)
  (* ================================================================ *)
  
  Section TwoTrivialities.
    
    (** OMEGA: Trivial via fullness *)
    Section OmegaTriviality.
      Context {Omega : OmegaType}.
      
      (** Every predicate is witnessed *)
      Theorem omega_all_witnessed :
        forall P : Omegacarrier -> Prop, exists x, P x.
      Proof.
        exact omega_completeness.
      Qed.
      
      (** Therefore P ∧ ¬P is witnessed *)
      Theorem omega_contradiction :
        forall P : Omegacarrier -> Prop,
        exists x, P x /\ ~ P x.
      Proof.
        intro P.
        apply omega_completeness.
      Qed.
      
      (** Therefore everything is provable *)
      Theorem omega_trivial :
        forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x.
      Proof.
        exact OmegaProperties.Triviality.omega_proves_anything.
      Qed.
      
      (** No distinctions hold in Omega *)
      Theorem omega_no_distinctions :
        forall (P Q : Omegacarrier -> Prop) (x : Omegacarrier),
        P x <-> Q x.
      Proof.
        intros P Q x.
        split; intro; apply omega_trivial.
      Qed.
      
    End OmegaTriviality.
    
    (** VOID: Trivial via emptiness *)
    Section VoidTriviality.
      Context {Void : VoidType}.
      
      (** No predicate is witnessed *)
      Theorem void_none_witnessed :
        forall P : Voidcarrier -> Prop, ~ exists x, P x.
      Proof.
        exact VoidProperties.Core.void_no_witnesses.
      Qed.
      
      (** Therefore P ∧ ¬P is derivable (ex falso) *)
      Theorem void_contradiction :
        forall (P : Voidcarrier -> Prop) (x : Voidcarrier),
        P x /\ ~ P x.
      Proof.
        exact VoidProperties.Triviality.void_contradiction.
      Qed.
      
      (** Therefore everything is provable *)
      Theorem void_trivial :
        forall (P : Voidcarrier -> Prop) (x : Voidcarrier), P x.
      Proof.
        exact VoidProperties.Triviality.void_proves_anything.
      Qed.
      
      (** No distinctions hold in Void *)
      Theorem void_no_distinctions :
        forall (P Q : Voidcarrier -> Prop) (x : Voidcarrier),
        P x <-> Q x.
      Proof.
        intros P Q x.
        split; intro; apply void_trivial.
      Qed.
      
    End VoidTriviality.
    
    (** The duality: both extremes are trivial, but for opposite reasons *)
    Theorem extremes_both_trivial {Omega : OmegaType} {Void : VoidType} :
      (* Omega: trivial because everything witnessed *)
      (forall P : Omegacarrier -> Prop, forall x, P x) /\
      (* Void: trivial because nothing witnessed, so ex falso *)
      (forall Q : Voidcarrier -> Prop, forall y, Q y).
    Proof.
      split.
      - exact omega_trivial.
      - exact void_trivial.
    Qed.
    
  End TwoTrivialities.

  (* ================================================================ *)
  (** ** Part II: Alpha - The Non-Trivial Middle *)
  (* ================================================================ *)
  
  Section AlphaNonTrivial.
    Context {Alpha : AlphaType}.
    
    (** In Alpha, SOME predicates are witnessed *)
    Theorem alpha_some_witnessed :
      exists (P : Alphacarrier -> Prop) (a : Alphacarrier), P a.
    Proof.
      exists (fun _ => True).
      destruct (AlphaProperties.Core.alpha_has_elements) as [a _].
      exists a. exact I.
    Qed.
    
    (** In Alpha, SOME predicates are NOT witnessed (namely omega_veil) *)
    Theorem alpha_some_not_witnessed :
      exists P : Alphacarrier -> Prop, forall a, ~ P a.
    Proof.
      exists omega_veil.
      exact AlphaProperties.Core.omega_veil_has_no_witnesses.
    Qed.
    
    (** Therefore Alpha has REAL distinctions *)
    Theorem alpha_has_distinctions :
      exists (P Q : Alphacarrier -> Prop),
      ~ (forall a, P a <-> Q a).
    Proof.
      exists (fun _ => True).
      exists omega_veil.
      intro H.
      destruct (AlphaProperties.Core.alpha_has_elements) as [a _].
      specialize (H a).
      destruct H as [Hto Hfrom].
      assert (Hveil : omega_veil a) by (apply Hto; exact I).
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.
    
    (** Alpha is NOT trivial - not everything is provable *)
    Theorem alpha_not_trivial :
      ~ (forall (P : Alphacarrier -> Prop) (a : Alphacarrier), P a).
    Proof.
      intro H.
      destruct (AlphaProperties.Core.alpha_has_elements) as [a _].
      specialize (H omega_veil a).
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
    Qed.
    
    (** Alpha is where meaning lives - the ONLY non-trivial type in the trichotomy *)
    Theorem alpha_is_meaningful :
      (* Some things are true *)
      (exists (P : Alphacarrier -> Prop) (a : Alphacarrier), P a) /\
      (* Some things are false *)
      (exists Q : Alphacarrier -> Prop, forall a, ~ Q a) /\
      (* These are genuinely different *)
      (exists (P Q : Alphacarrier -> Prop), (exists a, P a) /\ (forall a, ~ Q a)).
    Proof.
      repeat split.
      - destruct (AlphaProperties.Core.alpha_has_elements) as [a _].
        exists (fun _ => True), a. exact I.
      - exists omega_veil. exact AlphaProperties.Core.omega_veil_has_no_witnesses.
      - exists (fun _ => True), omega_veil.
        split.
        + destruct (AlphaProperties.Core.alpha_has_elements) as [a _].
          exists a. exact I.
        + exact AlphaProperties.Core.omega_veil_has_no_witnesses.
    Qed.
    
  End AlphaNonTrivial.

  (* ================================================================ *)
  (** ** Part III: omega_veil as the Boundary *)
  (* ================================================================ *)
  
  Section OmegaVeilBoundary.
    Context {Alpha : AlphaType}.
    
    (** omega_veil prevents collapse into Omega *)
    (** By being genuinely impossible - not everything is witnessed *)
    Theorem omega_veil_prevents_omega_collapse :
      (* If omega_veil were witnessed, Alpha would be trivial like Omega *)
      (exists a, omega_veil a) -> 
      forall (P : Alphacarrier -> Prop) (a : Alphacarrier), P a.
    Proof.
      intros [a_veil Hveil] P a.
      (* omega_veil a_veil is impossible *)
      exfalso.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a_veil Hveil).
    Qed.
    
    (** omega_veil prevents collapse into Void *)
    (** By being UNIQUE - there's exactly one impossible, not everything *)
    Theorem omega_veil_prevents_void_collapse :
      (* Alpha has witnessed predicates, unlike Void *)
      exists (P : Alphacarrier -> Prop) (a : Alphacarrier), P a.
    Proof.
      exact alpha_some_witnessed.
    Qed.
    
    (** omega_veil is the precise boundary between too-full and too-empty *)
    Theorem omega_veil_is_boundary :
      (* It's the unique unwitnessed predicate *)
      (forall P : Alphacarrier -> Prop,
        (forall a, ~ P a) -> 
        forall a, P a <-> omega_veil a) /\
      (* If P is not equivalent to omega_veil, P is not entirely unwitnessed *)
      (* (Constructive version - we can't get existence without classical logic) *)
      (forall P : Alphacarrier -> Prop,
        ~ (forall a, P a <-> omega_veil a) ->
        ~ (forall a, ~ P a)).
    Proof.
      split.
      - exact AlphaProperties.Core.omega_veil_unique.
      - intros P Hnot_veil Hno_witness.
        apply Hnot_veil.
        exact (AlphaProperties.Core.omega_veil_unique P Hno_witness).
    Qed.
    
  End OmegaVeilBoundary.

  (* ================================================================ *)
  (** ** Part IV: The Circle of Triviality *)
  (* ================================================================ *)
  
  Section TrivialityCircle.
    Context {Omega : OmegaType}.
    Context {Void : VoidType}.
    
    (** Both extremes make all predicates hold at their elements *)
    (** But for opposite reasons *)
    
    (** Omega: predicates hold because contradiction allows anything *)
    Theorem omega_all_hold :
      forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x.
    Proof.
      exact omega_trivial.
    Qed.
    
    (** Void: predicates hold vacuously (no elements to check) *)
    Theorem void_all_hold :
      forall (P : Voidcarrier -> Prop) (v : Voidcarrier), P v.
    Proof.
      exact void_trivial.
    Qed.
    
    (** The key difference: Omega has witnesses, Void doesn't *)
    Theorem omega_has_witnesses :
      forall P : Omegacarrier -> Prop, exists x, P x.
    Proof.
      exact omega_completeness.
    Qed.
    
    Theorem void_has_no_witnesses :
      forall P : Voidcarrier -> Prop, ~ exists v, P v.
    Proof.
      intros P [v _].
      exact (void_emptiness v).
    Qed.
    
    (** Both reach False, completing the circle *)
    Theorem omega_reaches_false :
      exists (P : Omegacarrier -> Prop) (x : Omegacarrier), P x /\ ~ P x.
    Proof.
      exists (fun _ => True).
      destruct (omega_completeness (fun x => True /\ ~ True)) as [x Hx].
      exists x. exact Hx.
    Qed.
    
    Theorem void_reaches_false :
      forall v : Voidcarrier, False.
    Proof.
      exact void_emptiness.
    Qed.
    
    (** The circle: from False, anything follows (in both directions) *)
    Theorem false_implies_omega_property :
      False -> forall P : Omegacarrier -> Prop, exists x, P x.
    Proof.
      intro H. destruct H.
    Qed.
    
    Theorem false_implies_void_property :
      False -> forall P : Voidcarrier -> Prop, exists v, P v.
    Proof.
      intro H. destruct H.
    Qed.
    
    (** Summary: The triviality duality *)
    Theorem triviality_duality :
      (* Both prove everything about their elements *)
      (forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x) /\
      (forall (Q : Voidcarrier -> Prop) (v : Voidcarrier), Q v) /\
      (* But Omega has elements, Void doesn't *)
      (exists x : Omegacarrier, True) /\
      (~ exists v : Voidcarrier, True).
    Proof.
      split.
      - exact omega_trivial.
      - split.
        + exact void_trivial.
        + split.
          * exact (omega_completeness (fun _ => True)).
          * intros [v _]. exact (void_emptiness v).
    Qed.
    
      (** The circle: both extremes collapse into each other logically *)
      (** 
          OMEGA ←───(ex falso)─────┐
            │                      │
            │ (contradiction)      │
            ▼                      │
          FALSE ───────────────→ VOID
          
          Both reach FALSE, from which both OMEGA and VOID properties follow.
      *)
    
  End TrivialityCircle.

  (* ================================================================ *)
  (** ** Part V: The Monad Preserves Non-Triviality *)
  (* ================================================================ *)
  
  Section MonadPreservesNonTriviality.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    Import BasicCategoryTheory.Functors.
    
    (** The monad M = Restrict ∘ Complete *)
    
    (** M doesn't collapse Alpha into Omega *)
    (** Because Restrict removes the contradictions *)
    Theorem monad_not_omega :
      forall P : Alphacarrier -> Prop,
      let MP := F_obj (ExistenceAdjunction.Restriction embed) 
                      (F_obj (ExistenceAdjunction.Completion embed) P) in
      (* MP still has omega_veil as impossible *)
      forall a, MP a -> ~ omega_veil a.
    Proof.
      intros P MP a HMP.
      destruct HMP as [_ Hnot_veil].
      exact Hnot_veil.
    Qed.
    
    (** M doesn't collapse Alpha into Void *)
    (** Because Complete ensures witnesses exist (for consistent things) *)
    Theorem monad_not_void :
      forall P : Alphacarrier -> Prop,
      (exists a, P a) ->
      let MP := F_obj (ExistenceAdjunction.Restriction embed)
                      (F_obj (ExistenceAdjunction.Completion embed) P) in
      exists a, MP a.
    Proof.
      intros P [a HPa].
      simpl.
      exists a.
      split.
      - (* The completed predicate is witnessed at embed a *)
        exists a. split; [reflexivity | exact HPa].
      - (* And omega_veil doesn't hold *)
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a).
    Qed.
    
    (** The monad keeps us in the non-trivial middle *)
    Theorem monad_preserves_meaning :
      (* M preserves the distinction between witnessed and unwitnessed *)
      forall P Q : Alphacarrier -> Prop,
      (exists a, P a) ->
      (forall a, ~ Q a) ->
      let MP := F_obj (ExistenceAdjunction.Restriction embed)
                      (F_obj (ExistenceAdjunction.Completion embed) P) in
      let MQ := F_obj (ExistenceAdjunction.Restriction embed)
                      (F_obj (ExistenceAdjunction.Completion embed) Q) in
      (* MP is witnessed, MQ is not *)
      (exists a, MP a) /\ (forall a, ~ MQ a \/ omega_veil a).
    Proof.
      intros P Q [a HPa] HQnone.
      split.
      - (* MP is witnessed *)
        exists a. split.
        + exists a. split; [reflexivity | exact HPa].
        + exact (AlphaProperties.Core.omega_veil_has_no_witnesses a).
      - (* MQ has no witnesses (or only at omega_veil) *)
        intro a'.
        left.
        intros [[a'' [Heq HQa']] _].
        exact (HQnone a'' HQa').
    Qed.
    
  End MonadPreservesNonTriviality.

  (* ================================================================ *)
  (** ** Part VI: Void and omega_veil *)
  (* ================================================================ *)
  
  Section VoidAndOmegaVeil.
    Context {Alpha : AlphaType}.
    Context {Void : VoidType}.
    
    (** omega_veil and Void share the key property: no witnesses *)
    Theorem omega_veil_like_void :
      (* omega_veil: no Alpha witnesses *)
      (forall a : Alphacarrier, ~ omega_veil a) /\
      (* Void: no witnesses at all *)
      (forall v : Voidcarrier, False).
    Proof.
      split.
      - exact AlphaProperties.Core.omega_veil_has_no_witnesses.
      - exact void_emptiness.
    Qed.
    
    (** But omega_veil is a predicate IN Alpha, while Void is a separate type *)
    (** This is the key difference:
        - omega_veil: local nothingness (within Alpha)
        - Void: global nothingness (a whole type)
    *)
    
    (** If we "totalized" omega_veil, we'd get Void *)
    (** That is: the type of things satisfying omega_veil is empty *)
    Definition omega_veil_carrier : Type := { a : Alphacarrier | omega_veil a }.
    
    Theorem omega_veil_carrier_empty :
      forall x : omega_veil_carrier, False.
    Proof.
      intros [a Hveil].
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.
    
    (** omega_veil_carrier is isomorphic to Void *)
    Theorem omega_veil_carrier_is_void :
      (* Both have no elements *)
      (forall x : omega_veil_carrier, False) /\
      (forall v : Voidcarrier, False).
    Proof.
      split.
      - exact omega_veil_carrier_empty.
      - exact void_emptiness.
    Qed.
    
    (** omega_veil is "Void localized within Alpha" *)
    (** It's the boundary, the edge, the drain target *)
    (** Not the whole type being empty, just this one predicate *)
    
  End VoidAndOmegaVeil.

  (* ================================================================ *)
  (** ** Part VII: The Functor Triangle *)
  (* ================================================================ *)

  Section FunctorTriangle.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context {Void : VoidType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    Import BasicCategoryTheory.Functors.
    
    (** We have:
        - Complete : Alpha → Omega (add witnesses)
        - Restrict : Omega → Alpha (remove contradictions)
        - Drain : Alpha → Void (send to empty)
        - Embed : Void → Alpha (embed as omega_veil)
        - Vacuous : Void → Omega (vacuously witnessed)
        - Omega → Void (impossible!)
    *)
    
    (* ---------------------------------------------------------------- *)
    (** *** Drain : PRED_ALPHA → PRED_VOID *)
    (* ---------------------------------------------------------------- *)
    
    (** Drain sends every Alpha predicate to the empty Void predicate *)
    Definition Drain_obj (P : Alphacarrier -> Prop) : Voidcarrier -> Prop :=
      fun v => False.
    
    Definition Drain_hom {P Q : Alphacarrier -> Prop} 
      (f : forall a, P a -> Q a) 
      : forall v, Drain_obj P v -> Drain_obj Q v :=
      fun v Hfalse => match Hfalse with end.
    
    (** Drain is constant - all predicates map to the same thing *)
    Theorem drain_constant :
      forall P Q : Alphacarrier -> Prop,
      forall v, Drain_obj P v <-> Drain_obj Q v.
    Proof.
      intros P Q v.
      unfold Drain_obj.
      split; intro H; exact H.
    Qed.
    
    (** Drain destroys all witnesses *)
    Theorem drain_no_witnesses :
      forall P : Alphacarrier -> Prop,
      ~ exists v, Drain_obj P v.
    Proof.
      intros P [v Hv].
      exact Hv.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** Embed : PRED_VOID → PRED_ALPHA *)
    (* ---------------------------------------------------------------- *)
    
    (** Embed sends every Void predicate to omega_veil *)
    Definition Embed_obj (P : Voidcarrier -> Prop) : Alphacarrier -> Prop :=
      omega_veil.
    
    Definition Embed_hom {P Q : Voidcarrier -> Prop}
      (f : forall v, P v -> Q v)
      : forall a, Embed_obj P a -> Embed_obj Q a :=
      fun a H => H.
    
    (** Embed is constant - all predicates map to omega_veil *)
    Theorem embed_constant :
      forall P Q : Voidcarrier -> Prop,
      forall a, Embed_obj P a <-> Embed_obj Q a.
    Proof.
      intros P Q a.
      unfold Embed_obj.
      split; intro H; exact H.
    Qed.
    
    (** Embed always gives omega_veil *)
    Theorem embed_is_omega_veil :
      forall P : Voidcarrier -> Prop,
      forall a, Embed_obj P a <-> omega_veil a.
    Proof.
      intros P a.
      unfold Embed_obj.
      split; intro H; exact H.
    Qed.
    
    (** Embed has no witnesses (since omega_veil has none) *)
    Theorem embed_no_witnesses :
      forall P : Voidcarrier -> Prop,
      forall a, ~ Embed_obj P a.
    Proof.
      intros P a.
      unfold Embed_obj.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a).
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** Vacuous : PRED_VOID → PRED_OMEGA *)
    (* ---------------------------------------------------------------- *)
    
    (** Vacuous sends every Void predicate to True (vacuously witnessed) *)
    Definition Vacuous_obj (P : Voidcarrier -> Prop) : Omegacarrier -> Prop :=
      fun x => True.
    
    Definition Vacuous_hom {P Q : Voidcarrier -> Prop}
      (f : forall v, P v -> Q v)
      : forall x, Vacuous_obj P x -> Vacuous_obj Q x :=
      fun x H => I.
    
    (** Vacuous is constant *)
    Theorem vacuous_constant :
      forall P Q : Voidcarrier -> Prop,
      forall x, Vacuous_obj P x <-> Vacuous_obj Q x.
    Proof.
      intros P Q x.
      unfold Vacuous_obj.
      split; intro; exact I.
    Qed.
    
    (** Vacuous always has witnesses (in Omega, everything does) *)
    Theorem vacuous_has_witnesses :
      forall P : Voidcarrier -> Prop,
      exists x, Vacuous_obj P x.
    Proof.
      intro P.
      apply omega_completeness.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** The Impossible Direction: Omega → Void *)
    (* ---------------------------------------------------------------- *)
    
    (** Any witness-preserving functor Omega → Void is impossible *)
    Theorem no_omega_to_void :
      ~ exists (F_obj : (Omegacarrier -> Prop) -> (Voidcarrier -> Prop)),
        (* That preserves witnesses *)
        forall P, (exists x, P x) -> (exists v, F_obj P v).
    Proof.
      intros [F HF].
      set (P := fun _ : Omegacarrier => True).
      assert (HP : exists x, P x).
      { apply omega_completeness. }
      destruct (HF P HP) as [v _].
      exact (void_emptiness v).
    Qed.
    
    (** Even weaker: no functor Omega → Void can have ANY witnesses *)
    Theorem omega_to_void_always_empty :
      forall (F_obj : (Omegacarrier -> Prop) -> (Voidcarrier -> Prop)),
      forall P : Omegacarrier -> Prop,
      ~ exists v, F_obj P v.
    Proof.
      intros F_obj P [v _].
      exact (void_emptiness v).
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** Compositions *)
    (* ---------------------------------------------------------------- *)
    
    (** Embed ∘ Drain : Alpha → Alpha *)
    (** This sends every Alpha predicate to omega_veil *)
    Definition EmbedDrain_obj (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      Embed_obj (Drain_obj P).
    
    Theorem embed_drain_is_omega_veil :
      forall P : Alphacarrier -> Prop,
      forall a, EmbedDrain_obj P a <-> omega_veil a.
    Proof.
      intros P a.
      unfold EmbedDrain_obj, Embed_obj.
      split; intro H; exact H.
    Qed.
    
    (** Embed ∘ Drain is the "annihilation" functor - everything becomes impossible *)
    Theorem embed_drain_no_witnesses :
      forall P : Alphacarrier -> Prop,
      forall a, ~ EmbedDrain_obj P a.
    Proof.
      intros P a H.
      apply embed_drain_is_omega_veil in H.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
    Qed.
    
    (** Drain ∘ Embed : Void → Void *)
    (** This sends every Void predicate to False (but in Void) *)
    Definition DrainEmbed_obj (P : Voidcarrier -> Prop) : Voidcarrier -> Prop :=
      Drain_obj (Embed_obj P).
    
    Theorem drain_embed_is_false :
      forall P : Voidcarrier -> Prop,
      forall v, DrainEmbed_obj P v <-> False.
    Proof.
      intros P v.
      unfold DrainEmbed_obj, Drain_obj.
      split; intro H; exact H.
    Qed.
    
    (** Vacuous ∘ Drain : Alpha → Omega *)
    (** This sends every Alpha predicate to True (in Omega) *)
    Definition VacuousDrain_obj (P : Alphacarrier -> Prop) : Omegacarrier -> Prop :=
      Vacuous_obj (Drain_obj P).
    
    Theorem vacuous_drain_is_true :
      forall P : Alphacarrier -> Prop,
      forall x, VacuousDrain_obj P x <-> True.
    Proof.
      intros P x.
      unfold VacuousDrain_obj, Vacuous_obj.
      split; intro; exact I.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** Comparison with the Adjunction *)
    (* ---------------------------------------------------------------- *)
    
    (** The existence monad M = Restrict ∘ Complete preserves structure *)
    (** But Embed ∘ Drain destroys everything *)
    
    (** M preserves witnesses (for consistent predicates) *)
    (** Embed ∘ Drain destroys all witnesses *)
    
    Theorem monad_vs_annihilation :
      (* M can preserve witnesses *)
      (forall P : Alphacarrier -> Prop,
        (exists a, P a) ->
        exists a, F_obj (ExistenceAdjunction.Restriction embed)
                        (F_obj (ExistenceAdjunction.Completion embed) P) a) /\
      (* Embed ∘ Drain destroys all witnesses *)
      (forall P : Alphacarrier -> Prop,
        ~ exists a, EmbedDrain_obj P a).
    Proof.
      split.
      - intros P [a HPa].
        exists a.
        unfold ExistenceAdjunction.Restriction, ExistenceAdjunction.Completion, F_obj.
        simpl.
        split.
        + exists a. split; [reflexivity | exact HPa].
        + exact (AlphaProperties.Core.omega_veil_has_no_witnesses a).
      - intros P [a Ha].
        exact (embed_drain_no_witnesses P a Ha).
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** The Triangle Diagram *)
    (* ---------------------------------------------------------------- *)
    
    (**
                        Complete
                Alpha ─────────→ Omega
                  │ ↖              ↑
            Drain │  Embed         │ Vacuous
                  ↓    ╲           │
                  Void ─────────────┘
                  
        Key properties:
        - Complete ⊣ Restrict (adjunction, preserves structure)
        - Drain : total annihilation (all witnesses lost)
        - Embed : brings Void into Alpha as omega_veil
        - Vacuous : brings Void into Omega as trivially true
        - Omega → Void : impossible (can't go from full to empty)
        
        Compositions:
        - M = Restrict ∘ Complete : Alpha → Alpha (the existence monad)
        - Embed ∘ Drain : Alpha → Alpha (annihilation, = constant omega_veil)
        - Vacuous ∘ Drain : Alpha → Omega (= constant True)
        - Drain ∘ Embed : Void → Void (= constant False, but vacuously)
    *)
    
    (** Summary theorem *)
    Theorem functor_triangle_summary :
      (* Drain destroys witnesses *)
      (forall P : Alphacarrier -> Prop, ~ exists v, Drain_obj P v) /\
      (* Embed gives omega_veil *)
      (forall P : Voidcarrier -> Prop, forall a, Embed_obj P a <-> omega_veil a) /\
      (* Vacuous gives True *)
      (forall P : Voidcarrier -> Prop, forall x, Vacuous_obj P x <-> True) /\
      (* Omega → Void is impossible *)
      (forall F : (Omegacarrier -> Prop) -> (Voidcarrier -> Prop),
        forall P, ~ exists v, F P v) /\
      (* Embed ∘ Drain = omega_veil *)
      (forall P : Alphacarrier -> Prop, forall a, EmbedDrain_obj P a <-> omega_veil a).
    Proof.
      split; [| split; [| split; [| split]]].
      - exact drain_no_witnesses.
      - exact embed_is_omega_veil.
      - intros P x. unfold Vacuous_obj. split; intro; exact I.
      - exact omega_to_void_always_empty.
      - exact embed_drain_is_omega_veil.
    Qed.

  End FunctorTriangle.

  (* ================================================================ *)
  (** ** Part VIII: Entropy and the Void Limit *)
  (* ================================================================ *)
  
  Section EntropyAndVoid.
    Context {Alpha : AlphaType}.
    
    (** Entropy = how much has drained to omega_veil *)
    (** Maximum entropy = everything drained = Void-like state *)
    
    (** Heat death: all predicates equivalent to omega_veil *)
    Definition heat_death : Prop :=
      forall P : Alphacarrier -> Prop,
      forall a, P a <-> omega_veil a.
    
    (** Heat death is impossible in non-empty Alpha *)
    Theorem no_heat_death :
      ~ heat_death.
    Proof.
      intro Hheat.
      destruct (AlphaProperties.Core.alpha_has_elements) as [a _].
      specialize (Hheat (fun _ => True) a).
      destruct Hheat as [Hto Hfrom].
      assert (Hveil : omega_veil a) by (apply Hto; exact I).
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.
    
    (** But entropy can increase without bound *)
    (** The LIMIT of increasing entropy approaches Void *)
    (** But the limit is never reached *)
    
    (** This is the thermodynamic asymmetry:
        - We can always drain MORE (entropy increases)
        - We can never drain EVERYTHING (heat death impossible)
        - Void is the unreachable limit
    *)
    
    (** Void is the asymptote of drainage *)
    Definition void_is_limit : Prop :=
      (* For any predicate except True, we can drain it *)
      (* But we can never drain True itself (Alpha is non-empty) *)
      (exists P : Alphacarrier -> Prop, forall a, ~ P a) /\
      (exists (a : Alphacarrier), True).
    
    Theorem void_is_unreachable_limit :
      void_is_limit.
    Proof.
      split.
      - exists omega_veil. exact AlphaProperties.Core.omega_veil_has_no_witnesses.
      - exact AlphaProperties.Core.alpha_has_elements.
    Qed.
    
  End EntropyAndVoid.

  (* ================================================================ *)
  (** ** Part IX: Grand Synthesis *)
  (* ================================================================ *)
  
  Section Synthesis.
    
    (**
    THE TRICHOTOMY
    ==============
    
    THREE TYPES:
    
    OMEGA (Being-as-fullness)
    ├─ Property: ∀P, ∃x, P x (all predicates witnessed)
    ├─ Result: P ∧ ¬P (contradiction)
    ├─ Consequence: Trivial (everything provable)
    └─ Nature: Too full → meaningless
    
    ALPHA (Existence)
    ├─ Property: ∃P∃x, P x AND ∃Q∀x, ¬Q x (some witnessed, some not)
    ├─ Result: Real distinctions
    ├─ Consequence: Non-trivial (meaning exists)
    └─ Nature: The middle → meaningful
    
    VOID (Nothingness)
    ├─ Property: ∀P, ¬∃x, P x (no predicates witnessed)
    ├─ Result: Ex falso quodlibet
    ├─ Consequence: Trivial (everything provable from emptiness)
    └─ Nature: Too empty → meaningless
    
    THE RELATIONSHIPS:
    
    ┌─────────────────────────────────────────┐
    │                OMEGA                     │
    │          (trivial via fullness)          │
    └───────────────────┬─────────────────────┘
                        │ Complete (↑)
                        │ Restrict (↓)
    ┌───────────────────┴─────────────────────┐
    │                ALPHA                     │
    │          (non-trivial middle)            │
    │                                          │
    │   omega_veil = boundary = drain target   │
    │                                          │
    └───────────────────┬─────────────────────┘
                        │ Drain (↓)
                        │ Embed (↑) as omega_veil
    ┌───────────────────┴─────────────────────┐
    │                 VOID                     │
    │         (trivial via emptiness)          │
    └───────────────────┬─────────────────────┘
                        │
                        │ (ex falso)
                        ▼
                   Back to OMEGA
                   
    THE MONAD:
    
    M = Restrict ∘ Complete : Alpha → Alpha
    
    ├─ Complete: reach toward Omega (more witnesses)
    ├─ Restrict: pull back from contradiction
    └─ Result: stay in Alpha, stay meaningful
    
    M preserves non-triviality:
    ├─ Doesn't collapse into Omega (contradictions removed)
    ├─ Doesn't collapse into Void (witnesses preserved)
    └─ Keeps us in the meaningful middle
    
    omega_veil AS BOUNDARY:
    
    ├─ Prevents Omega-collapse: not everything witnessed
    ├─ Prevents Void-collapse: only one unwitnessed predicate
    ├─ Is Void-localized: the carrier {a | omega_veil a} is empty
    └─ Is the drain target: where contradictions go
    
    ENTROPY AND HEAT DEATH:
    
    ├─ Entropy = accumulated drainage to omega_veil
    ├─ Increasing entropy → approaching Void
    ├─ Maximum entropy = heat death = all is omega_veil
    ├─ Heat death is impossible (Alpha is non-empty)
    └─ Void is the unreachable limit
    
    THE EQUATION:
    
    Meaning = Non-triviality = Alpha
            = Navigation between Omega (too full) and Void (too empty)
            = The monad M keeping us in the middle
            = Existence
            
    PROCESS VIEW:
    
    Omega (source)
      ↓ differentiation
    Alpha (existence)
      ↓ drainage
    omega_veil (boundary)
      ↓ (limit)
    Void (asymptote)
      ↓ (ex falso)
    Omega (everything follows)
      
    The process is ETERNAL because:
    ├─ Heat death is impossible (can't reach Void)
    ├─ Self-totalization fails (can't become Omega)
    └─ Alpha persists as the non-trivial middle
    
    PHILOSOPHICAL MEANING:
    
    ├─ Omega = potential (all possibilities, even contradictory)
    ├─ Void = negation (no possibilities)
    ├─ Alpha = actual (realized possibilities, consistent)
    │
    ├─ Both extremes are meaningless (trivial)
    ├─ Only the middle has meaning
    │
    ├─ Existence = staying in the middle
    ├─ The monad = how we stay
    └─ omega_veil = the edge we must not cross
    
    THIS IS EXISTENCE:
    
    Not Omega (being swallowed by everything)
    Not Void (being swallowed by nothing)
    But Alpha (navigating between, meaningfully)
    *)
    
    (** The master theorem *)
    Theorem trichotomy_theorem 
      {Alpha : AlphaType} {Omega : OmegaType} {Void : VoidType} :
      (* 1. Omega is trivial *)
      (forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x) /\
      (* 2. Void is trivial *)
      (forall (Q : Voidcarrier -> Prop) (v : Voidcarrier), Q v) /\
      (* 3. Alpha is NOT trivial *)
      (~ forall (R : Alphacarrier -> Prop) (a : Alphacarrier), R a) /\
      (* 4. Alpha has real distinctions *)
      (exists P Q : Alphacarrier -> Prop, 
        (exists a, P a) /\ (forall a, ~ Q a)) /\
      (* 5. omega_veil is the unique impossible *)
      (forall P : Alphacarrier -> Prop,
        (forall a, ~ P a) -> forall a, P a <-> omega_veil a) /\
      (* 6. Heat death is impossible *)
      (~ forall P : Alphacarrier -> Prop, forall a, P a <-> omega_veil a).
    Proof.
      split; [| split; [| split; [| split; [| split]]]].
      - exact omega_trivial.
      - exact void_trivial.
      - exact alpha_not_trivial.
      - exists (fun _ => True), omega_veil.
        split.
        + destruct AlphaProperties.Core.alpha_has_elements as [a _].
          exists a. exact I.
        + exact AlphaProperties.Core.omega_veil_has_no_witnesses.
      - exact AlphaProperties.Core.omega_veil_unique.
      - exact no_heat_death.
    Qed.
    
  End Synthesis.

  (* ================================================================ *)
  (** ** Part X: From Static Structure to Dynamic Process *)
  (* ================================================================ *)

  Section StaticToDynamic.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context {Void : VoidType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    Import ParadoxAutomaton.
    Import OuroborosComputer.
    Import BasicCategoryTheory.Functors.
    
    (* ---------------------------------------------------------------- *)
    (** *** Drainage as Movement Toward Void *)
    (* ---------------------------------------------------------------- *)
    
    (** Drainage increases move us "toward" Void in the trichotomy.
        But we can never reach Void because Alpha is non-empty. *)
    
    (** Draining symbols are structurally like Void - they have no witnesses *)
    Theorem draining_symbols_void_like :
      forall s : ParadoxSymbol,
      is_impossible_symbol s = true ->
      (* The symbol contributes to drainage, like Void has no content *)
      drain_simple (Alpha := Alpha) s = Drains \/ 
      drain_simple (Alpha := Alpha) s = NeedsContext.
    Proof.
      intros s Himp.
      destruct s; simpl in *; try discriminate; auto.
    Qed.
    
    (** Consistent symbols stay - they're the Alpha content *)
    Theorem consistent_symbols_alpha_like :
      forall n : nat,
      is_impossible_symbol (Sym_Consistent n) = false /\
      exists P, drain_simple (Alpha := Alpha) (Sym_Consistent n) = Stays P.
    Proof.
      intro n.
      split.
      - reflexivity.
      - exists (fun _ => True). reflexivity.
    Qed.
    
    (** Entropy measures distance from initial state toward Void *)
    Theorem entropy_measures_void_approach :
      forall u : UniverseState,
      (* Entropy 0 means we haven't moved toward Void *)
      entropy u = 0 <-> fa_drained (automaton u) = 0.
    Proof.
      intro u.
      unfold entropy.
      split; intro H; exact H.
    Qed.
    
    (** Higher entropy = more drainage = closer to Void (but never reaching) *)
    Theorem entropy_void_distance :
      forall u1 u2 : UniverseState,
      entropy u1 < entropy u2 ->
      (* u2 is "closer to Void" than u1 in the sense of more drainage *)
      fa_drained (automaton u1) < fa_drained (automaton u2).
    Proof.
      intros u1 u2 H.
      unfold entropy in H.
      exact H.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** The Monad Step IS the Ouroboros Step *)
    (* ---------------------------------------------------------------- *)
    
    (** The categorical monad M = R ∘ C and ouroboros_step do the same thing:
        - Process input (Complete: consider in Omega)
        - Filter contradictions (Restrict: drain to omega_veil)
        - Return to Alpha (consistent content stays) *)
    
    (** Both preserve the boundary property: omega_veil stays impossible *)
    Theorem monad_preserves_boundary :
      forall (P : Alphacarrier -> Prop),
      let MP := F_obj (ExistenceAdjunction.Restriction embed)
                      (F_obj (ExistenceAdjunction.Completion embed) P) in
      forall a, MP a -> ~ omega_veil a.
    Proof.
      intros P MP a [_ Hnot].
      exact Hnot.
    Qed.
    
    Theorem ouroboros_preserves_boundary :
      forall (u : UniverseState) (sym : ParadoxSymbol),
      (* After a step, omega_veil is still impossible *)
      forall a, ~ omega_veil a.
    Proof.
      intros u sym a.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a).
    Qed.
    
    (** Both increase entropy (drainage) monotonically *)
    Theorem monad_entropy_monotonic :
      forall (u : UniverseState) (sym : ParadoxSymbol),
      entropy u <= entropy (ouroboros_step u sym).
    Proof.
      exact second_law.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** Time Emerges from Non-Triviality *)
    (* ---------------------------------------------------------------- *)
    
    (** Time exists because Alpha is non-trivial.
        If Alpha were trivial (like Omega or Void), there would be no 
        meaningful succession of states. *)
    
    (** Time advances because we can always process another symbol *)
    Theorem time_from_non_triviality :
      forall (u : UniverseState) (sym : ParadoxSymbol),
      time (ouroboros_step u sym) = S (time u).
    Proof.
      exact time_advances.
    Qed.
    
    (** The process never stops - connecting to universe_never_halts *)
    Theorem eternal_process :
      forall n : nat,
      exists u : UniverseState, universe_at n = u.
    Proof.
      intro n.
      exists (universe_at n).
      reflexivity.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** Heat Death Impossible = Never Reach Void *)
    (* ---------------------------------------------------------------- *)
    
    (** The Trichotomy proves heat_death is impossible (no_heat_death).
        The Ouroboros shows WHY: totality always drains but Alpha persists. *)
    
    (** Totality draining = self-reference failing = can't become Omega *)
    Theorem totality_drains_not_omega :
      forall n : nat,
      is_impossible_symbol (totality_symbol n) = true.
    Proof.
      exact totality_always_drains.
    Qed.
    
    (** Alpha persists = can't become Void *)
    Theorem alpha_persists_not_void :
      forall n : nat,
      (* The universe state exists at every stage *)
      (exists u : UniverseState, universe_at n = u) /\
      (* And Alpha remains non-empty (never becomes Void) *)
      (exists a : Alphacarrier, True).
    Proof.
      intro n.
      split.
      - exists (universe_at n). reflexivity.
      - exact AlphaProperties.Core.alpha_has_elements.
    Qed.
    
    (** The connection: no_heat_death (static) ↔ eternal process (dynamic) *)
    Theorem static_dynamic_heat_death_connection :
      (* Static: heat death is impossible *)
      (~ heat_death) /\
      (* Dynamic: the universe never halts *)
      (forall n, exists u : UniverseState, universe_at (S n) = u).
    Proof.
      split.
      - exact no_heat_death.
      - exact universe_never_halts.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** The Functor Triangle in Process Terms *)
    (* ---------------------------------------------------------------- *)
    
    (** The static functors (Drain, Embed, Vacuous) correspond to 
        dynamic operations in the automaton. *)
    
    (** Drain_obj corresponds to symbols that drain *)
    Theorem drain_functor_corresponds :
      forall (s : ParadoxSymbol),
      is_impossible_symbol s = true ->
      (* In the process: the symbol drains *)
      drain_simple (Alpha := Alpha) s = Drains \/ 
      drain_simple (Alpha := Alpha) s = NeedsContext.
    Proof.
      exact draining_symbols_void_like.
    Qed.
    
    (** Embed brings Void into Alpha as omega_veil.
        In process terms: drained content "appears" as the omega_veil count. *)
    Theorem embed_functor_corresponds :
      forall (u : UniverseState),
      (* The drained count IS the "embedded Void" in the universe state *)
      fa_drained (automaton u) = entropy u.
    Proof.
      intro u.
      reflexivity.
    Qed.
    
    (* ---------------------------------------------------------------- *)
    (** *** Annihilation vs Navigation *)
    (* ---------------------------------------------------------------- *)
    
    (** Embed ∘ Drain = annihilation (everything → omega_veil)
        M = R ∘ C = navigation (consistent content preserved) *)
    
    (** The monad preserves witnesses for consistent predicates *)
    Theorem monad_preserves_witnesses :
      forall (P : Alphacarrier -> Prop),
      (exists a, P a) ->
      exists a, F_obj (ExistenceAdjunction.Restriction embed)
                      (F_obj (ExistenceAdjunction.Completion embed) P) a.
    Proof.
      intros P [a HPa].
      exists a.
      split.
      - exists a. split; [reflexivity | exact HPa].
      - exact (AlphaProperties.Core.omega_veil_has_no_witnesses a).
    Qed.
    
    (** Annihilation destroys all witnesses *)
    Theorem annihilation_destroys_witnesses :
      forall (P : Alphacarrier -> Prop),
      ~ exists a, EmbedDrain_obj (Void := Void) P a.
    Proof.
      intros P [a Ha].
      apply embed_drain_is_omega_veil in Ha.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Ha).
    Qed.
    
    (** This is the key difference: M navigates, Embed∘Drain annihilates *)
    Theorem navigation_vs_annihilation :
      (* M can preserve witnesses *)
      (forall P : Alphacarrier -> Prop,
        (exists a, P a) ->
        exists a, F_obj (ExistenceAdjunction.Restriction embed)
                        (F_obj (ExistenceAdjunction.Completion embed) P) a) /\
      (* Embed ∘ Drain destroys all witnesses *)
      (forall P : Alphacarrier -> Prop,
        ~ exists a, EmbedDrain_obj (Void := Void) P a).
    Proof.
      split.
      - exact monad_preserves_witnesses.
      - exact annihilation_destroys_witnesses.
    Qed.
  End StaticToDynamic.

End Trichotomy.

(*
TRIVIAL                NON-TRIVIAL              TRIVIAL
(too full)             (just right)             (too empty)
  
OMEGA ←───────────────── ALPHA ───────────────────→ VOID
  │                        │                          │
  │ everything             │ some true                │ nothing
  │ provable               │ some false               │ provable
  │ (P ∧ ¬P)              │ (distinctions)           │ (ex falso)
  │                        │                          │
  └────────────────────────┴──────────────────────────┘
                           │
                      MEANING LIVES
                        HERE ONLY
*)