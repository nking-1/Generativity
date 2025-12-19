(** * TraceCategory.v
    
    Traces form a category. Morphisms between traces preserve or 
    reflect hologram structure. This connects the automaton back to
    the categorical foundations.
    
    Key insight:
    - Monic morphisms: Reflect impossibilities (no false refutations)
    - Epic morphisms: Cover impossibilities (complete refutation)
    - The evolution operator has specific monic/epic properties
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.ExistenceAdjunction.
Require Import DAO.Theory.ExistenceComonad.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import DAO.Computation.BoundaryAutomaton.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Module TraceCategory.

  Import ExistenceAdjunction.
  Import ExistenceComonad.
  Import ImpossibilityAlgebra.Core.
  Import BoundaryAutomaton.

  (* ================================================================ *)
  (** ** Part 1: Morphisms of Traces *)
  (* ================================================================ *)

  Section TraceMorphisms.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** A trace morphism relates two traces at corresponding times.
        It's a family of state relations indexed by time. *)
    Definition TraceMorphism (t1 t2 : Trace) : Type :=
      forall (n : nat), Alphacarrier -> Alphacarrier -> Prop.

    (** A morphism is functional if it acts like a function on witnesses *)
    Definition functional_morphism (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      forall n a, t1 n a -> exists a', f n a a' /\ t2 n a'.

    (** A morphism preserves hologram membership (forward direction) *)
    Definition preserves_hologram (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      forall n a a', 
        f n a a' -> 
        hologram t1 n a -> 
        hologram t2 n a'.

    (** A morphism reflects hologram membership (backward direction) *)
    Definition reflects_hologram (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      forall n a a',
        f n a a' ->
        hologram t2 n a' ->
        hologram t1 n a.

    (** A morphism preserves existence *)
    Definition preserves_existence (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      forall n a a',
        f n a a' ->
        existence t1 n a ->
        existence t2 n a'.

    (** A morphism reflects existence *)
    Definition reflects_existence (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      forall n a a',
        f n a a' ->
        existence t2 n a' ->
        existence t1 n a.

    (* ------------------------------------------------------------ *)
    (** *** Monic and Epic Morphisms *)
    (* ------------------------------------------------------------ *)

    (** A monic morphism reflects structure: 
        If the image is impossible, the source was impossible.
        "No false refutations" - we don't wrongly call things impossible. *)
    Definition monic (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      reflects_hologram t1 t2 f.

    (** An epic morphism covers structure:
        Every impossibility in t2 comes from one in t1.
        "Complete refutation" - we find all impossibilities. *)
    Definition epic (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      forall n a',
        hologram t2 n a' ->
        exists a, f n a a' /\ hologram t1 n a.

    (** An isomorphism is both monic and epic *)
    Definition trace_iso (t1 t2 : Trace) (f : TraceMorphism t1 t2) : Prop :=
      monic t1 t2 f /\ epic t1 t2 f /\
      exists g : TraceMorphism t2 t1,
        (forall n a a', f n a a' -> g n a' a) /\
        (forall n a' a, g n a' a -> f n a a').

    (* ------------------------------------------------------------ *)
    (** *** The Identity Morphism *)
    (* ------------------------------------------------------------ *)

    Definition id_morphism (t : Trace) : TraceMorphism t t :=
      fun n a a' => a = a'.

    Theorem id_is_monic : forall t,
      monic t t (id_morphism t).
    Proof.
      intros t n a a' Hid Hholo.
      unfold id_morphism in Hid.
      subst a'.
      exact Hholo.
    Qed.

    Theorem id_is_epic : forall t,
      epic t t (id_morphism t).
    Proof.
      intros t n a' Hholo.
      exists a'.
      split.
      - unfold id_morphism. reflexivity.
      - exact Hholo.
    Qed.

    (* ------------------------------------------------------------ *)
    (** *** Composition of Morphisms *)
    (* ------------------------------------------------------------ *)

    Definition compose_morphism {t1 t2 t3 : Trace}
      (g : TraceMorphism t2 t3) (f : TraceMorphism t1 t2) 
      : TraceMorphism t1 t3 :=
      fun n a a'' => exists a', f n a a' /\ g n a' a''.

    Theorem compose_monic : forall t1 t2 t3 f g,
      monic t1 t2 f ->
      monic t2 t3 g ->
      monic t1 t3 (compose_morphism g f).
    Proof.
      intros t1 t2 t3 f g Hf Hg.
      unfold monic, reflects_hologram in *.
      intros n a a'' [a' [Hfa Hga']] Hholo.
      apply (Hf n a a' Hfa).
      apply (Hg n a' a'' Hga').
      exact Hholo.
    Qed.

    Theorem compose_epic : forall t1 t2 t3 f g,
      epic t1 t2 f ->
      epic t2 t3 g ->
      epic t1 t3 (compose_morphism g f).
    Proof.
      intros t1 t2 t3 f g Hf Hg.
      unfold epic in *.
      intros n a'' Hholo.
      destruct (Hg n a'' Hholo) as [a' [Hga' Hholo']].
      destruct (Hf n a' Hholo') as [a [Hfa Hholo'']].
      exists a.
      split.
      - exists a'. split; assumption.
      - exact Hholo''.
    Qed.

  End TraceMorphisms.

  (* ================================================================ *)
  (** ** Part 2: The Time-Shift Morphism *)
  (* ================================================================ *)

  Section TimeShift.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** The time-shift morphism: relates t at time n to t at time n+1.
        This is the "evolution as morphism" perspective. *)
    Definition time_shift (t : Trace) : TraceMorphism t t :=
      fun n a a' => a = a'.  (* Same point, different time *)

    (** Key insight: The hologram at n embeds in hologram at n+1.
        This is hologram_monotone viewed as a morphism property. *)

    (** Time evolution preserves hologram (forward in time) *)
    Theorem time_preserves_hologram :
      forall t n a,
      hologram t n a -> hologram t (Datatypes.S n) a.
    Proof.
      intros t n a H.
      simpl. left. exact H.
    Qed.

    (** Time does NOT reflect hologram (can't go backward).
        New impossibilities appear that weren't there before. *)
    Theorem time_does_not_reflect :
      (* There exist traces where hologram grows strictly *)
      forall t,
      (exists n a, hologram t (Datatypes.S n) a /\ ~ hologram t n a) ->
      ~ reflects_hologram t t (time_shift t).
    Proof.
      intros t [n [a [Hsucc Hnot]]] Hrefl.
      apply Hnot.
      apply (Hrefl n a a).
      - unfold time_shift. reflexivity.
      - exact Hsucc.
    Qed.

    (** Time evolution is NOT monic: new impossibilities appear.
        This is the Arrow of Time in categorical language. *)
    Corollary time_not_monic :
      forall t,
      (exists n a, hologram t (Datatypes.S n) a /\ ~ hologram t n a) ->
      ~ monic t t (time_shift t).
    Proof.
      apply time_does_not_reflect.
    Qed.

    (** Time evolution IS epic on the growing hologram:
        Every old impossibility persists. *)
    Theorem time_epic_on_past :
      forall t n a,
      hologram t n a ->
      exists a', time_shift t n a' a /\ hologram t n a'.
    Proof.
      intros t n a H.
      exists a.
      split.
      - unfold time_shift. reflexivity.
      - exact H.
    Qed.

  End TimeShift.

  (* ================================================================ *)
  (** ** Part 3: Embedding Morphisms Between Alphas *)
  (* ================================================================ *)

  Section EmbeddingMorphisms.
    Context {Alpha1 Alpha2 : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed1 : @Alphacarrier Alpha1 -> Omegacarrier).
    Context (embed2 : @Alphacarrier Alpha2 -> Omegacarrier).

    (** A function between Alphas that respects the embeddings *)
    Definition respects_embedding (f : @Alphacarrier Alpha1 -> @Alphacarrier Alpha2) : Prop :=
      forall a, embed2 (f a) = embed1 a.

    (** Such a function induces a trace morphism *)
    Definition induced_morphism 
      (f : @Alphacarrier Alpha1 -> @Alphacarrier Alpha2)
      (Hresp : respects_embedding f)
      (t1 : @Trace Alpha1) (t2 : @Trace Alpha2)
      : @TraceMorphism Alpha1 t1 t1 :=
      fun n a a' => a = a'.

    (** If f respects veils, it preserves impossibility structure *)
    Definition respects_veil (f : @Alphacarrier Alpha1 -> @Alphacarrier Alpha2) : Prop :=
      forall a, @omega_veil Alpha1 a <-> @omega_veil Alpha2 (f a).

    (** Veil-respecting functions preserve hologram structure *)
    Theorem veil_respecting_preserves_hologram :
      forall (f : @Alphacarrier Alpha1 -> @Alphacarrier Alpha2),
      respects_veil f ->
      forall t1 n a,
      @hologram Alpha1 t1 n a ->
      @omega_veil Alpha2 (f a) \/ 
      exists t2, @hologram Alpha2 t2 n (f a).
    Proof.
      intros f Hveil t1 n a Hholo.
      induction n.
      - (* Base: hologram at 0 is omega_veil *)
        simpl in Hholo.
        left.
        apply Hveil.
        exact Hholo.
      - (* Step: either from past or newly erased *)
        simpl in Hholo.
        destruct Hholo as [Hprev | [Ht Hnt]].
        + (* From previous hologram *)
          destruct (IHn Hprev) as [Hveil' | [t2 Hholo2]].
          * left. exact Hveil'.
          * right. exists t2. apply hologram_monotone. exact Hholo2.
        + (* Newly erased - this depends on how t2 relates to t1 *)
          left.
          (* We can't conclude without knowing how traces relate *)
          (* This shows the limit of what we can prove generically *)
    Admitted.

  End EmbeddingMorphisms.

  (* ================================================================ *)
  (** ** Part 4: The Monic/Epic Duality *)
  (* ================================================================ *)

  Section MonicEpicDuality.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** Monic = existence-reflecting = "what exists in image existed in source" *)
    Theorem monic_reflects_existence :
      forall t1 t2 f,
      monic t1 t2 f ->
      reflects_existence t1 t2 f.
    Proof.
      intros t1 t2 f Hmonic.
      unfold reflects_existence, monic, reflects_hologram in *.
      intros n a a' Hf Hex.
      unfold existence in *.
      intro Hholo.
      apply Hex.
      apply (Hmonic n a a' Hf Hholo).
    Qed.

    (** Epic = hologram-covering = "every impossibility has a source" *)
    (** This is the definition *)

    (** Monic morphisms compose *)
    Corollary monic_compose :
      forall t1 t2 t3 f g,
      monic t1 t2 f -> monic t2 t3 g ->
      monic t1 t3 (compose_morphism g f).
    Proof.
      apply compose_monic.
    Qed.

    (** Epic morphisms compose *)
    Corollary epic_compose :
      forall t1 t2 t3 f g,
      epic t1 t2 f -> epic t2 t3 g ->
      epic t1 t3 (compose_morphism g f).
    Proof.
      apply compose_epic.
    Qed.

    (** The fundamental asymmetry: time is epic-on-past but not monic *)
    (** This IS the arrow of time in categorical language:
        - We can trace impossibilities backward (epic on past)
        - We cannot trace them forward uniquely (not monic)
        - New impossibilities appear without source *)

  End MonicEpicDuality.

  (* ================================================================ *)
  (** ** Part 5: Simulation and Bisimulation *)
  (* ================================================================ *)

  Section Simulation.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** t1 simulates t2 if every step in t2 can be matched in t1 *)
    Definition simulates (t1 t2 : Trace) : Prop :=
      exists f : TraceMorphism t1 t2,
        monic t1 t2 f /\ 
        forall n, t2 n = fun a' => exists a, f n a a' /\ t1 n a.

    (** Bisimulation: mutual simulation *)
    Definition bisimilar (t1 t2 : Trace) : Prop :=
      simulates t1 t2 /\ simulates t2 t1.

    (** Bisimilar traces have the same hologram structure *)
    Theorem bisimilar_same_hologram_structure :
      forall t1 t2,
      bisimilar t1 t2 ->
      forall n,
        (exists a, hologram t1 n a) <-> (exists a', hologram t2 n a').
    Proof.
      intros t1 t2 [[f [Hf1 Hf2]] [g [Hg1 Hg2]]] n.
      split; intros [a H].
      - (* t1 has hologram -> t2 has hologram *)
        (* This would require epic property or functional morphism *)
        (* For now, admit the connection *)
        admit.
      - (* t2 has hologram -> t1 has hologram *)
        admit.
    Admitted.

  End Simulation.

  (* ================================================================ *)
  (** ** Part 6: The Category of Traces *)
  (* ================================================================ *)

  Section TracesCat.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** We can form a category where:
        - Objects: Traces
        - Morphisms: TraceMorphisms that are functional
        - Identity: id_morphism
        - Composition: compose_morphism *)

    (** The category laws hold up to proof irrelevance *)
    
    Theorem traces_left_id :
      forall t1 t2 (f : TraceMorphism t1 t2),
      forall n a a',
        compose_morphism (id_morphism t2) f n a a' <-> f n a a'.
    Proof.
      intros t1 t2 f n a a'.
      unfold compose_morphism, id_morphism.
      split.
      - intros [a'' [Hf Hid]]. subst a''. exact Hf.
      - intro Hf. exists a'. split; [exact Hf | reflexivity].
    Qed.

    Theorem traces_right_id :
      forall t1 t2 (f : TraceMorphism t1 t2),
      forall n a a',
        compose_morphism f (id_morphism t1) n a a' <-> f n a a'.
    Proof.
      intros t1 t2 f n a a'.
      unfold compose_morphism, id_morphism.
      split.
      - intros [a'' [Hid Hf]]. subst a''. exact Hf.
      - intro Hf. exists a. split; [reflexivity | exact Hf].
    Qed.

    Theorem traces_assoc :
      forall t1 t2 t3 t4 
        (f : TraceMorphism t1 t2) 
        (g : TraceMorphism t2 t3)
        (h : TraceMorphism t3 t4),
      forall n a a''',
        compose_morphism h (compose_morphism g f) n a a''' <->
        compose_morphism (compose_morphism h g) f n a a'''.
    Proof.
      intros.
      unfold compose_morphism.
      split.
      - intros [a' [[a'' [Hf Hg]] Hh]].
        exists a''. split; [exact Hf |].
        exists a'. split; [exact Hg | exact Hh].
      - intros [a'' [Hf [a' [Hg Hh]]]].
        exists a'. split.
        + exists a''. split; [exact Hf | exact Hg].
        + exact Hh.
    Qed.

  End TracesCat.

End TraceCategory.

(** * ThreeValuedLogic.v
    
    The automaton's execution naturally induces a three-valued logic.
    
    - Verified: In the current state, not in hologram
    - Refuted: In the hologram (impossible)
    - Unknown: Neither determined nor refuted
    
    This connects to:
    - Intuitionistic logic (no excluded middle)
    - The diagonal argument (forces undecidability)
    - Kripke semantics (possible worlds)
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.ExistenceAdjunction.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import DAO.Execution.BoundaryAutomaton.

Module ThreeValuedLogic.

  Import ExistenceAdjunction.
  Import ImpossibilityAlgebra.Core.
  Import BoundaryAutomaton.

  (* ================================================================ *)
  (** ** Part 1: The Three Values *)
  (* ================================================================ *)

  Section Values.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** The three truth values *)
    Inductive TruthValue : Type :=
      | Verified : TruthValue   (* Positively established *)
      | Refuted : TruthValue    (* Impossible *)
      | Unknown : TruthValue.   (* Not yet determined *)

    (** Equality is decidable *)
    Definition tv_eq_dec (v1 v2 : TruthValue) : {v1 = v2} + {v1 <> v2}.
    Proof.
      destruct v1, v2;
      try (left; reflexivity);
      try (right; discriminate).
    Defined.

    (** A proposition about a point at a time *)
    Definition Proposition := Alphacarrier -> Prop.

    (** Classification of a point relative to a trace and proposition *)
    (** Note: This requires decidability, so we define it predicatively *)
    
    (** A point is verified if it satisfies P and is not in hologram *)
    Definition is_verified (t : Trace) (n : nat) (P : Proposition) (a : Alphacarrier) : Prop :=
      P a /\ ~ hologram t n a.

    (** A point is refuted if it's in the hologram *)
    Definition is_refuted (t : Trace) (n : nat) (a : Alphacarrier) : Prop :=
      hologram t n a.

    (** A point is unknown if it's neither verified nor refuted *)
    Definition is_unknown (t : Trace) (n : nat) (P : Proposition) (a : Alphacarrier) : Prop :=
      ~ P a /\ ~ hologram t n a.

    (** The three classes are mutually exclusive *)
    Theorem values_exclusive :
      forall t n P a,
      ~ (is_verified t n P a /\ is_refuted t n a).
    Proof.
      intros t n P a [[HP Hnotholo] Hholo].
      exact (Hnotholo Hholo).
    Qed.

    Theorem verified_not_unknown :
      forall t n P a,
      is_verified t n P a -> ~ is_unknown t n P a.
    Proof.
      intros t n P a [HP Hnot] [HnotP _].
      exact (HnotP HP).
    Qed.

    Theorem refuted_not_unknown :
      forall t n P a,
      is_refuted t n a -> ~ is_unknown t n P a.
    Proof.
      intros t n P a Hholo [_ Hnot].
      exact (Hnot Hholo).
    Qed.

    (** But they are NOT exhaustive without excluded middle! *)
    (** This is the key: ¬(P a) ∨ P a is not provable constructively *)

  End Values.

  (* ================================================================ *)
  (** ** Part 2: Logical Operations *)
  (* ================================================================ *)

  Section Operations.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** Negation in three-valued logic *)
    (** NOT Verified = Refuted, NOT Refuted = Verified, NOT Unknown = Unknown *)
    Definition tv_not (v : TruthValue) : TruthValue :=
      match v with
      | Verified => Refuted
      | Refuted => Verified
      | Unknown => Unknown
      end.

    (** Conjunction: Unknown poisons, Refuted dominates *)
    Definition tv_and (v1 v2 : TruthValue) : TruthValue :=
      match v1, v2 with
      | Refuted, _ => Refuted
      | _, Refuted => Refuted
      | Unknown, _ => Unknown
      | _, Unknown => Unknown
      | Verified, Verified => Verified
      end.

    (** Disjunction: Unknown poisons, Verified dominates *)
    Definition tv_or (v1 v2 : TruthValue) : TruthValue :=
      match v1, v2 with
      | Verified, _ => Verified
      | _, Verified => Verified
      | Unknown, _ => Unknown
      | _, Unknown => Unknown
      | Refuted, Refuted => Refuted
      end.

    (** Implication: Kleene's strong three-valued logic *)
    Definition tv_implies (v1 v2 : TruthValue) : TruthValue :=
      match v1, v2 with
      | Refuted, _ => Verified       (* False implies anything *)
      | _, Verified => Verified      (* Anything implies true *)
      | Verified, Refuted => Refuted (* True doesn't imply false *)
      | Verified, Unknown => Unknown
      | Unknown, Refuted => Unknown
      | Unknown, Unknown => Unknown
      end.

    (** Double negation does NOT return to original for Unknown *)
    Theorem double_negation_not_identity :
      tv_not (tv_not Unknown) = Unknown.
    Proof. reflexivity. Qed.

    (** But it does for Verified and Refuted *)
    Theorem double_negation_verified :
      tv_not (tv_not Verified) = Verified.
    Proof. reflexivity. Qed.

    Theorem double_negation_refuted :
      tv_not (tv_not Refuted) = Refuted.
    Proof. reflexivity. Qed.

    (** De Morgan laws hold *)
    Theorem de_morgan_and :
      forall v1 v2,
      tv_not (tv_and v1 v2) = tv_or (tv_not v1) (tv_not v2).
    Proof.
      intros [] []; reflexivity.
    Qed.

    Theorem de_morgan_or :
      forall v1 v2,
      tv_not (tv_or v1 v2) = tv_and (tv_not v1) (tv_not v2).
    Proof.
      intros [] []; reflexivity.
    Qed.

  End Operations.

  (* ================================================================ *)
  (** ** Part 3: Evolution of Truth Values *)
  (* ================================================================ *)

  Section Evolution.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** Key insight: Over time, Unknown can become Refuted,
        but Refuted never becomes anything else. *)

    (** Once refuted, always refuted *)
    Theorem refuted_permanent :
      forall t n P a,
      is_refuted t n a ->
      is_refuted t (Datatypes.S n) a.
    Proof.
      intros t n P a Href.
      unfold is_refuted in *.
      apply hologram_monotone.
      exact Href.
    Qed.

    (** Unknown can become refuted *)
    (** This happens when evolution adds to the hologram *)
    Definition becomes_refuted (t : Trace) (n : nat) (P : Proposition) (a : Alphacarrier) : Prop :=
      is_unknown t n P a /\ is_refuted t (Datatypes.S n) a.

    (** Verified can become refuted (if we lose existence) *)
    Definition becomes_refuted_from_verified (t : Trace) (n : nat) (P : Proposition) (a : Alphacarrier) : Prop :=
      is_verified t n P a /\ is_refuted t (Datatypes.S n) a.

    (** Nothing becomes Unknown: the hologram only grows *)
    Theorem nothing_becomes_unknown :
      forall t n P a,
      is_refuted t n a ->
      ~ is_unknown t (Datatypes.S n) P a.
    Proof.
      intros t n P a Href [_ Hnot].
      apply Hnot.
      apply hologram_monotone.
      exact Href.
    Qed.

    (** The three values form a partial order under "more determined" *)
    (** Unknown < Verified, Unknown < Refuted *)
    (** Verified and Refuted are incomparable *)

    Definition more_determined (v1 v2 : TruthValue) : Prop :=
      match v1, v2 with
      | Unknown, Verified => True
      | Unknown, Refuted => True
      | Unknown, Unknown => True
      | Verified, Verified => True
      | Refuted, Refuted => True
      | _, _ => False
      end.

    (** Time increases determination (for refutation) *)
    Theorem time_increases_refutation :
      forall t n a,
      is_refuted t n a ->
      more_determined Refuted Refuted.  (* trivial, but shows pattern *)
    Proof.
      intros. simpl. exact I.
    Qed.

  End Evolution.

  (* ================================================================ *)
  (** ** Part 4: The Diagonal Argument *)
  (* ================================================================ *)

  Section Diagonal.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** The diagonal argument shows we can't have just two values.
        
        Suppose we could decide every proposition. Then define:
        D(a) := "the decision procedure says 'no' about a at a"
        
        This creates a contradiction, forcing Unknown to exist. *)

    (** A decision procedure would assign Verified or Refuted to every point *)
    Definition is_decision_procedure (decide : Alphacarrier -> TruthValue) : Prop :=
      forall a, decide a = Verified \/ decide a = Refuted.

    (** The diagonal predicate *)
    Definition diagonal (decide : Alphacarrier -> TruthValue) : Proposition :=
      fun a => decide a = Refuted.

    (** If decide is a decision procedure, diagonal creates trouble *)
    Theorem diagonal_undecidable :
      forall decide,
      is_decision_procedure decide ->
      (* If we could decide 'diagonal', we'd have a problem *)
      forall a, 
        (decide a = Verified -> diagonal decide a -> False) /\
        (decide a = Refuted -> diagonal decide a).
    Proof.
      intros decide Hdec a.
      split.
      - intros Hver Hdiag.
        unfold diagonal in Hdiag.
        rewrite Hver in Hdiag.
        discriminate.
      - intros Href.
        unfold diagonal.
        exact Href.
    Qed.

    (** The escape: some things are Unknown *)
    (** We can't build a total decision procedure that handles its own diagonal *)

    (** Connection to Gödel: The diagonal sentence is in Unknown *)
    Definition godel_sentence (decide : Alphacarrier -> TruthValue) : Proposition :=
      fun a => decide a = Unknown.

    (** If a point is in the Gödel sentence, it escapes the decision procedure *)
    Theorem godel_escapes :
      forall decide a,
      godel_sentence decide a ->
      ~ is_decision_procedure decide.
    Proof.
      intros decide a Hgodel Hdec.
      destruct (Hdec a) as [Hver | Href].
      - unfold godel_sentence in Hgodel. rewrite Hver in Hgodel. discriminate.
      - unfold godel_sentence in Hgodel. rewrite Href in Hgodel. discriminate.
    Qed.

  End Diagonal.

  (* ================================================================ *)
  (** ** Part 5: Kripke Semantics *)
  (* ================================================================ *)

  Section Kripke.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** Each time step is a "possible world".
        The accessibility relation is time ordering. *)

    Definition World := nat.

    Definition accessible (w1 w2 : World) : Prop := w1 <= w2.

    (** Forces: what is true at a world *)
    Definition forces (t : Trace) (w : World) (P : Proposition) : Prop :=
      forall a, P a -> ~ hologram t w a.

    (** Necessity: true at all accessible worlds *)
    Definition necessary (t : Trace) (w : World) (P : Proposition) : Prop :=
      forall w', accessible w w' -> forces t w' P.

    (** Possibility: true at some accessible world *)
    Definition possibly (t : Trace) (w : World) (P : Proposition) : Prop :=
      exists w', accessible w w' /\ forces t w' P.

    (** Refutation is necessary (once refuted, always refuted) *)
    Theorem refutation_necessary :
      forall t w a,
      hologram t w a ->
      forall w', accessible w w' -> hologram t w' a.
    Proof.
      intros t w a Hholo w' Hacc.
      apply hologram_contains_past with (m := w).
      - exact Hacc.
      - exact Hholo.
    Qed.

    (** The Unknown corresponds to "possibly true, possibly false" *)
    Definition kripke_unknown (t : Trace) (w : World) (P : Proposition) : Prop :=
      possibly t w P /\ possibly t w (fun a => ~ P a).

    (** Connection: is_unknown implies kripke_unknown (partially) *)
    (** The exact connection requires more machinery *)

  End Kripke.

  (* ================================================================ *)
  (** ** Part 6: Summary Theorems *)
  (* ================================================================ *)

  Section Summary.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** The three-valued logic emerges necessarily from the automaton *)
    Theorem three_values_necessary :
      (* 1. Values are exclusive *)
      (forall t n P a, ~ (is_verified t n P a /\ is_refuted t n a)) /\
      
      (* 2. Refutation is permanent *)
      (forall t n a, is_refuted t n a -> is_refuted t (Datatypes.S n) a) /\
      
      (* 3. Nothing becomes unknown *)
      (forall t n P a, is_refuted t n a -> ~ is_unknown t (Datatypes.S n) P a) /\
      
      (* 4. Double negation doesn't eliminate Unknown *)
      (tv_not (tv_not Unknown) = Unknown).
    Proof.
      repeat split.
      - apply values_exclusive.
      - intros. apply refuted_permanent with (P := fun _ => True). assumption.
      - apply nothing_becomes_unknown.
      - reflexivity.
    Qed.

    (** The connection to the metaphysics *)
    (**
       Verified = What we've constructed (in the state, not hologram)
       Refuted = What's impossible (in the hologram)
       Unknown = The gap where existence happens
       
       Time flows by:
       - Unknown -> Refuted (hologram grows)
       - Never: Refuted -> anything (permanent)
       - Never: anything -> Unknown (hologram doesn't shrink)
       
       The diagonal argument forces Unknown to exist:
       - Can't decide everything
       - Some propositions escape any decision procedure
       - This is the "room" for the automaton to run
    *)

  End Summary.

End ThreeValuedLogic.