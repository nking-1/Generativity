(** * BoundaryAutomaton.v
    
    A formal model of existence as computation at the boundary
    between consistency (Alpha) and totality (Omega).
    
    The automaton runs on the M ⊣ W adjunction:
    - State lives in Alpha (consistent hypotheses)
    - Evolution via M = R ∘ C (propose then filter)
    - Observation via W = C ∘ R (complete the restriction)
    
    Core insight: Existence computes by not becoming impossible.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.ExistenceAdjunction.
Require Import DAO.Theory.ExistenceComonad.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import DAO.Theory.CategoryTheory.
Import BasicCategoryTheory.Core.
Import BasicCategoryTheory.Constructions.
Import BasicCategoryTheory.Functors.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.PropExtensionality.

Module BoundaryAutomaton.

  Import ExistenceAdjunction.
  Import ExistenceComonad.
  Import ImpossibilityAlgebra.Core.

  (* ================================================================ *)
  (** ** Part 1: The State Space *)
  (* ================================================================ *)

  Section StateSpace.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (** A State is an Alpha-predicate: a hypothesis about what exists.
        It lives in the consistent fragment. *)
    Definition State := Alphacarrier -> Prop.

    (** An Observation is an Omega-predicate: what totality "sees".
        It lives in the complete (but trivial) space. *)
    Definition Observation := Omegacarrier -> Prop.

    (** The canonical impossible state: omega_veil itself *)
    Definition void_state : State := omega_veil.

    (** The canonical trivial state: a proposition true everywhere *)
    Definition full_state : State := fun _ => True.

    (** A state is possible if it's not equivalent to omega_veil *)
    Definition possible (S : State) : Prop := Is_Possible S.

    (** A state is impossible if it collapses to omega_veil *)
    Definition impossible (S : State) : Prop := Is_Impossible S.

    (** Void state is impossible *)
    Theorem void_is_impossible : impossible void_state.
    Proof.
      unfold impossible, void_state, Is_Impossible.
      intro a. reflexivity.
    Qed.

    (** Full state is possible (assuming Alpha is non-empty) *)
    Theorem full_is_possible : possible full_state.
    Proof.
      unfold possible, full_state, Is_Possible, Is_Impossible.
      intro H.
      destruct alpha_not_empty as [a _].
      specialize (H a).
      destruct H as [Hforward _].
      assert (Htrue : True) by exact I.
      apply Hforward in Htrue.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Htrue).
    Qed.

    (* ================================================================ *)
    (** ** Part 2: The Transition Operators *)
    (* ================================================================ *)

    (** Shorthand for our functors - see ExistenceAdjunction.v *)
    Let C := Completion embed.
    Let R := Restriction embed.

    (* ------------------------------------------------------------ *)
    (** *** Lifting and Projecting *)
    (* ------------------------------------------------------------ *)

    (** Lift: State → Observation (via Completion)
        "Extend the hypothesis to all of Omega" *)
    Definition lift (S : State) : Observation :=
      fun x => exists a, embed a = x /\ S a.

    (** Project: Observation → State (via Restriction)  
        "Extract the consistent part" *)
    Definition project (Q : Observation) : State :=
      fun a => Q (embed a) /\ ~ omega_veil a.

    (** Lift is exactly Completion *)
    Lemma lift_is_completion : forall S,
      lift S = F_obj C S.
    Proof. reflexivity. Qed.

    (** Project is exactly Restriction *)
    Lemma project_is_restriction : forall Q,
      project Q = F_obj R Q.
    Proof. reflexivity. Qed.

    (* ------------------------------------------------------------ *)
    (** *** The Monad Step: M = R ∘ C *)
    (* ------------------------------------------------------------ *)

    (** Evolve: One round-trip through Omega
        "Propose a completion, then filter back to consistency" *)
    Definition evolve (S : State) : State :=
      project (lift S).

    (** Evolve is exactly M *)
    Lemma evolve_is_M : forall S,
      evolve S = M embed S.
    Proof. reflexivity. Qed.

    (** Evolve explicitly *)
    Lemma evolve_unfold : forall S a,
      evolve S a <-> 
      (exists a', embed a' = embed a /\ S a') /\ ~ omega_veil a.
    Proof.
      intros S a.
      unfold evolve, project, lift.
      reflexivity.
    Qed.

    (* ------------------------------------------------------------ *)
    (** *** The Comonad Filter: W = C ∘ R *)
    (* ------------------------------------------------------------ *)

    (** Filter: Modal necessity on observations
        "What must hold from all Alpha perspectives" *)
    Definition filter (Q : Observation) : Observation :=
      W embed Q.

    (** Filter explicitly *)
    Lemma filter_unfold : forall Q x,
      filter Q x <->
      exists a, embed a = x /\ Q (embed a) /\ ~ omega_veil a.
    Proof.
      intros Q x.
      apply W_unfold.
    Qed.

    (* ------------------------------------------------------------ *)
    (** *** The Full Step: Project ∘ Filter ∘ Lift *)
    (* ------------------------------------------------------------ *)

    (** Step: Full cycle through the adjunction
        State → Omega → filtered Omega → State *)
    Definition step (S : State) : State :=
      project (filter (lift S)).

    (** Key theorem: step = M ∘ M (double evolution) *)
    Theorem step_is_M_squared : forall S,
      step S = evolve (evolve S).
    Proof.
      intro S.
      unfold step, evolve, project, lift, filter.
      unfold W, F_obj, Completion, Restriction.
      simpl.
      extensionality a.
      apply propositional_extensionality.
      split.
      - (* step S a -> evolve (evolve S) a *)
        intros [Hex Hnot].
        destruct Hex as [a' [Heq [[a'' [Heq' HSa'']] Hnot']]].
        split.
        + exists a'.
          split; [exact Heq |].
          split.
          * exists a''. split; [exact Heq' | exact HSa''].
          * exact Hnot'.
        + exact Hnot.
      - (* evolve (evolve S) a -> step S a *)
        intros [[a' [Heq [[a'' [Heq' HSa'']] Hnot']]] Hnot].
        split.
        + exists a'.
          split; [exact Heq |].
          split.
          * exists a''. split; [exact Heq' | exact HSa''].
          * exact Hnot'.
        + exact Hnot.
    Qed.

    (** The W layer adds another M iteration *)
    Corollary filter_adds_iteration : forall S,
      project (filter (lift S)) = M embed (M embed S).
    Proof.
      intro S.
      rewrite <- evolve_is_M.
      apply step_is_M_squared.
    Qed.

    (* ================================================================ *)
    (** ** Part 3: Evolution Properties *)
    (* ================================================================ *)

    (** Evolution preserves structure (via monad functor laws) *)
    
    (** Key: If st is impossible, evolve st is impossible *)
    Theorem evolve_preserves_impossible :
      forall st : State,
      impossible st -> impossible (evolve st).
    Proof.
      intros st Himp.
      unfold impossible, Is_Impossible in *.
      intro a.
      split.
      - intro Hev.
        apply evolve_unfold in Hev.
        destruct Hev as [[a' [Heq Hsta']] Hnot].
        apply Himp in Hsta'.
        exfalso.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a' Hsta').
      - intro Hveil.
        exfalso.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.

    (** Evolution filters out the veiled *)
    Theorem evolve_excludes_veil :
      forall st a,
      evolve st a -> ~ omega_veil a.
    Proof.
      intros st a Hev.
      apply evolve_unfold in Hev.
      destruct Hev as [_ Hnot].
      exact Hnot.
    Qed.

    (** Iterated evolution *)
    Fixpoint evolve_n (n : nat) (st : State) : State :=
      match n with
      | O => st
      | S m => evolve (evolve_n m st)
      end.

    (** evolve_n 1 = evolve *)
    Lemma evolve_n_1 : forall st, evolve_n 1 st = evolve st.
    Proof. reflexivity. Qed.

    (** evolve_n (S n) = evolve ∘ evolve_n n *)
    Lemma evolve_n_succ : forall n st,
      evolve_n (S n) st = evolve (evolve_n n st).
    Proof. reflexivity. Qed.

    (** step = evolve_n 2 *)
    Theorem step_is_evolve_2 : forall st,
      step st = evolve_n 2 st.
    Proof.
      intro st.
      rewrite step_is_M_squared.
      reflexivity.
    Qed.

    (* ================================================================ *)
    (** ** Part 4: Traces and Execution *)
    (* ================================================================ *)

    (** A Trace is a sequence of states indexed by time *)
    Definition Trace := nat -> State.

    (** The initial state of a trace *)
    Definition initial (t : Trace) : State := t 0.

    (** A trace follows evolution if each state evolves to the next *)
    Definition follows_evolve (t : Trace) : Prop :=
      forall n, t (S n) = evolve (t n).

    (** A trace follows the full step *)
    Definition follows_step (t : Trace) : Prop :=
      forall n, t (S n) = step (t n).

    (** Generate a trace from an initial state via evolution *)
    Fixpoint generate_trace (S0 : State) (n : nat) : State :=
      match n with
      | O => S0
      | S m => evolve (generate_trace S0 m)
      end.

    (** Generated traces follow evolution *)
    Theorem generated_follows : forall S0,
      follows_evolve (generate_trace S0).
    Proof.
      intros S0 n.
      reflexivity.
    Qed.

    (** Generate via step (double evolution per tick) *)
    Fixpoint generate_trace_step (S0 : State) (n : nat) : State :=
      match n with
      | O => S0
      | S m => step (generate_trace_step S0 m)
      end.

    (** Generated step-traces follow step *)
    Theorem generated_step_follows : forall S0,
      follows_step (generate_trace_step S0).
    Proof.
      intros S0 n.
      reflexivity.
    Qed.

    (* ================================================================ *)
    (** ** Part 5: The Hologram (Accumulated Impossibilities) *)
    (* ================================================================ *)

    (** A HolographicLayer is a predicate that adds a new 'No' to the world. *)
    Definition HolographicLayer := State.

    (** The hologram at step n: all impossibilities discovered so far.
        
        It starts with omega_veil (the primordial boundary) and 
        accumulates what gets "erased" at each step. *)
    Fixpoint hologram (t : Trace) (n : nat) : State :=
      match n with
      | O => omega_veil
      | S m => fun a => 
          hologram t m a \/           (* Previously impossible *)
          (t m a /\ ~ t (S m) a)      (* Newly erased *)
      end.

    (** Metaphysical Note: While the Hologram is a sum (OR) of impossible regions, 
        the constraint it imposes is a product (AND) of universal negations. *)

    (** Existence at step n: the complement of the hologram.
        We exist where the Hologram is not. Existence is a hypothesis to be refuted. *)
    Definition existence (t : Trace) (n : nat) : State :=
      fun a => ~ hologram t n a.

    Section PureImpossibilityHologram.

      (** We define P1, P2, and P3 as predicates that ARE impossible.
          They are not just 'failing' for some x; they are extensionally 
          equal to the omega_veil. *)
      Variables P1 P2 P3 : Alphacarrier -> Prop.
      Hypothesis H1 : Is_Impossible P1.
      Hypothesis H2 : Is_Impossible P2.
      Hypothesis H3 : Is_Impossible P3.

      (** The Hologram is the logical sum (OR).
          Because each component is impossible, the sum is ALSO impossible. *)
      Definition formal_hologram : State := 
        fun a => P1 a \/ P2 a \/ P3 a.

      Theorem hologram_is_formally_impossible : 
        Is_Impossible formal_hologram.
      Proof.
        unfold Is_Impossible, formal_hologram.
        intro a.
        split.
        - (* If any part of the hologram holds, omega_veil holds *)
          intros [HP1 | [HP2 | HP3]].
          + apply H1. exact HP1.
          + apply H2. exact HP2.
          + apply H3. exact HP3.
        - (* If omega_veil holds, the hologram (vacuously) holds *)
          intro Hov. left. apply H1. exact Hov.
      Qed.

      (** Existence as the Refutation:
          Existence a <-> (P1 a \/ P2 a \/ P3 a -> False) *)
      Definition existence_state : State := 
        fun a => ~ (formal_hologram a).

      (** The De Morgan unfolding:
          Existence is the product of the refutations of each veil. *)
      Theorem existence_refutes_all_veils :
        forall a, existence_state a <-> (P1 a -> False) /\ (P2 a -> False) /\ (P3 a -> False).
      Proof.
        intros a. unfold existence_state, formal_hologram.
        split.
        - intro Hneg. repeat split; intro HP; apply Hneg; auto.
        - intros [Hn1 [Hn2 Hn3]] [HP1 | [HP2 | HP3]].
          + exact (Hn1 HP1).
          + exact (Hn2 HP2).
          + exact (Hn3 HP3).
      Qed.

    End PureImpossibilityHologram.

    (** The hologram only grows *)
    Theorem hologram_monotone :
      forall t n a,
      hologram t n a -> hologram t (S n) a.
    Proof.
      intros t n a H.
      simpl. left. exact H.
    Qed.

    (** Existence only shrinks *)
    Theorem existence_antitone :
      forall t n a,
      existence t (S n) a -> existence t n a.
    Proof.
      intros t n a Hex Hprev.
      apply Hex.
      apply hologram_monotone.
      exact Hprev.
    Qed.

    (** omega_veil is in all holograms *)
    Theorem veil_always_in_hologram :
      forall t n a,
      omega_veil a -> hologram t n a.
    Proof.
      intros t n a Hveil.
      induction n.
      - simpl. exact Hveil.
      - simpl. left. exact IHn.
    Qed.

    (** existence excludes omega_veil *)
    Theorem existence_excludes_veil :
      forall t n a,
      existence t n a -> ~ omega_veil a.
    Proof.
      intros t n a Hex Hveil.
      apply Hex.
      apply veil_always_in_hologram.
      exact Hveil.
    Qed.

    (** If the trace follows evolution, evolved states exclude the veiled *)
    Theorem trace_excludes_veil :
      forall t,
      follows_evolve t ->
      forall n a,
      t (S n) a -> ~ omega_veil a.
    Proof.
      intros t Hfollows n a Hta.
      rewrite Hfollows in Hta.
      apply (evolve_excludes_veil (t n) a Hta).
    Qed.

    Section ExistenceRefutation.
      (** Helper to provide a generic layers function for the trial *)
      Variable layers : nat -> HolographicLayer.
      Variable t : Trace.

      (** The TRIAL:
          If you give me a witness 'a' that satisfies the Hologram, 
          I derive a contradiction. *)
      Definition trial (n : nat) (a : Alphacarrier) : Prop :=
        hologram t n a -> False.

      (** THEOREM: existence_is_the_trial *)
      Theorem existence_is_the_trial :
        forall n a, 
        existence t n a <-> trial n a.
      Proof.
        intros n a. reflexivity.
      Qed.

      (** METAPHYSICAL CORE: The "Hypothetical Witness" Theorem. *)
      Theorem survivor_refutes_the_veil :
        forall n a,
        existence t n a -> 
        forall (P_n : State),
        Is_Impossible P_n ->
        (P_n a -> False).
      Proof.
        intros n a Hex P_n Himp HPa.
        apply Himp in HPa.
        (* We use the general property that existence excludes the primordial veil *)
        apply existence_excludes_veil in Hex.
        exact (Hex HPa).
      Qed.

    End ExistenceRefutation.

    (* ================================================================ *)
    (** ** Part 6: Halting and Termination *)
    (* ================================================================ *)

    (** A trace halts at step n if the state becomes impossible *)
    Definition halts_at (t : Trace) (n : nat) : Prop :=
      impossible (t n).

    (** A trace has halted by step n if it halted at some m ≤ n *)
    Definition halted_by (t : Trace) (n : nat) : Prop :=
      exists m, m <= n /\ halts_at t m.

    (** A trace never halts if all states are possible *)
    Definition never_halts (t : Trace) : Prop :=
      forall n, possible (t n).

    (** Halting is permanent: once halted, always halted *)
    Theorem halting_permanent :
      forall t n,
      follows_evolve t ->
      halts_at t n ->
      halts_at t (S n).
    Proof.
      intros t n Hfollows Hhalt.
      unfold halts_at.
      rewrite Hfollows.
      apply evolve_preserves_impossible.
      exact Hhalt.
    Qed.

    (** Halting propagates forward *)
    Theorem halting_propagates :
      forall t n m,
      follows_evolve t ->
      halts_at t n ->
      n <= m ->
      halts_at t m.
    Proof.
      intros t n m Hfollows Hhalt Hle.
      induction Hle.
      - exact Hhalt.
      - apply halting_permanent; assumption.
    Qed.

    (** Total erasure: the hologram covers all of Alpha *)
    Definition total_erasure (t : Trace) (n : nat) : Prop :=
      forall a, hologram t n a.

    (** Total erasure implies halting (existence becomes impossible) *)
    Theorem erasure_implies_halt :
      forall t n,
      total_erasure t n ->
      impossible (existence t n).
    Proof.
      intros t n Htotal.
      unfold impossible, Is_Impossible.
      intro a.
      split.
      - intro Hex.
        unfold existence in Hex.
        exfalso.
        apply Hex.
        apply Htotal.
      - intro Hveil.
        exfalso.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.

    (* ================================================================ *)
    (** ** Part 7: The Arrow of Time *)
    (* ================================================================ *)

    (** Time's arrow emerges from hologram accumulation.
        We cannot go backward because we cannot "unerase" the hologram. *)

    (** The hologram at step n contains all previous holograms *)
    Theorem hologram_contains_past :
      forall t n m,
      m <= n ->
      forall a, hologram t m a -> hologram t n a.
    Proof.
      intros t n m Hle.
      induction Hle.
      - (* m = n *) trivial.
      - (* m <= n -> m <= S n *)
        intro a. intro H.
        apply hologram_monotone.
        apply IHHle.
        exact H.
    Qed.

    (** The past is implied by the present *)
    Theorem past_from_present :
      forall t n m a,
      m <= n ->
      existence t n a -> existence t m a.
    Proof.
      intros t n m a Hle Hex Hpast.
      apply Hex.
      apply (hologram_contains_past t n m Hle a Hpast).
    Qed.

    (** Size of existence (informally: entropy is hologram size) *)
    (** We can't directly measure size, but we can state:
        - More hologram = less existence = higher entropy
        - Time flows in direction of hologram growth *)

    (** The hologram is the "memory" of the universe *)
    Definition memory (t : Trace) (n : nat) : State :=
      hologram t n.

    (** Memory only grows *)
    Theorem memory_monotone :
      forall t n a,
      memory t n a -> memory t (S n) a.
    Proof.
      apply hologram_monotone.
    Qed.

    (** The universe cannot forget *)
    Theorem no_forgetting :
      forall t n m,
      m <= n ->
      forall a, memory t m a -> memory t n a.
    Proof.
      apply hologram_contains_past.
    Qed.

    (* ================================================================ *)
    (** ** Part 8: Modal Logic of the Automaton *)
    (* ================================================================ *)

    (** Import modal operators from ExistenceComonad *)

    (** Necessity: What must be true (survives W) *)
    Definition necessary (Q : Observation) : Observation :=
      box embed Q.

    (** Possibility: What could be true (not necessarily false) *)
    Definition possibly (Q : Observation) : Observation :=
      diamond embed Q.

    (** A state is necessary if its lift survives the filter *)
    Definition state_necessary (S : State) : Prop :=
      forall x, lift S x -> necessary (lift S) x.

    (** A state is contingent if it's possible but not necessary *)
    Definition state_contingent (S : State) : Prop :=
      possible S /\ 
      exists a, lift S (a) /\ ~ necessary (lift S) (a).

    (** The automaton runs on contingent states *)
    (** Necessary states are fixed points; impossible states are halted *)

    (** Necessary states are fixed under evolution 
        (This connects to W-coalgebras being fixed points) *)
    Theorem necessary_fixed :
      forall S,
      (forall a, S a <-> evolve S a) ->
      state_necessary S.
    Proof.
      intros S Hfixed x Hlift.
      unfold necessary, box, W, lift in *.
      simpl.
      destruct Hlift as [a [Heq HSa]].
      exists a.
      split; [exact Heq |].
      split.
      - exists a. split; [reflexivity | exact HSa].
      - (* Need ~ omega_veil a *)
        (* From Hfixed: S a <-> evolve S a *)
        (* evolve S a requires ~ omega_veil a *)
        apply Hfixed in HSa.
        apply evolve_unfold in HSa.
        destruct HSa as [_ Hnot].
        exact Hnot.
    Qed.

    (* ================================================================ *)
    (** ** Part 9: Connection to W-Coalgebras *)
    (* ================================================================ *)

    (** Import W-coalgebra structure *)

    (** A state is W-stable if its lift is W-coalgebraic *)
    Definition W_stable (S : State) : Prop :=
      is_W_coalgebraic embed (lift S).

    (** W-stable states are fixed points of the automaton *)
    Theorem W_stable_is_fixed :
      forall S,
      W_stable S ->
      forall x, lift S x <-> filter (lift S) x.
    Proof.
      intros S Hstable x.
      unfold W_stable, is_W_coalgebraic in Hstable.
      exact (Hstable x).
    Qed.

    (** Every Alpha predicate induces a W-coalgebra *)
    Definition state_to_coalgebra (S : State) : WCoalgebra embed :=
      alpha_to_coalgebra embed S.

    (** The automaton finds W-coalgebraic fixed points *)
    (** States that evolve without change are exactly W-coalgebras *)

    (* ================================================================ *)
    (** ** Part 10: Summary Theorems *)
    (* ================================================================ *)

    (** The Fundamental Theorem of the Boundary Automaton *)
    (* Theorem boundary_automaton_fundamental :
      (* 1. Evolution is via the monad *)
      (forall S, evolve S = M embed S) /\
      
      (* 2. Step is double evolution *)
      (forall S, step S = evolve (evolve S)) /\
      
      (* 3. Hologram only grows *)
      (forall t n a, hologram t n a -> hologram t (S n) a) /\
      
      (* 4. Existence only shrinks *)
      (forall t n a, existence t (S n) a -> existence t n a) /\
      
      (* 5. Halting is permanent *)
      (forall t n, 
        follows_evolve t -> 
        halts_at t n -> 
        halts_at t (S n)) /\
      
      (* 6. omega_veil is always in the hologram *)
      (forall t n a, omega_veil a -> hologram t n a).
    Proof.
      repeat split.
      - apply evolve_is_M.
      - apply step_is_M_squared.
      - apply hologram_monotone.
      - apply existence_antitone.
      - apply halting_permanent.
      - apply veil_always_in_hologram.
    Qed. *)

    (** Existence is computation that avoids contradiction *)
    (* Theorem existence_is_computation :
      forall t,
      follows_evolve t ->
      (* A point exists at time n iff it's not in the hologram *)
      (forall n a, existence t n a <-> ~ hologram t n a) /\
      (* Existence at n implies existence at all m < n *)
      (forall n m a, m <= n -> existence t n a -> existence t m a) /\
      (* The veiled never exist *)
      (forall n a, omega_veil a -> ~ existence t n a).
    Proof.
      intros t Hfollows.
      repeat split.
      - (* Definition of existence *)
        intros n' a'. reflexivity.
      - (* Past from present *)
        apply past_from_present.
      - (* Veiled don't exist *)
        intros n a Hveil Hex.
        apply Hex.
        apply veil_always_in_hologram.
        exact Hveil.
    Qed. *)
  
  End StateSpace.

End BoundaryAutomaton.