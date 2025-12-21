(** * ParadoxAutomaton.v
    
    Finite Paradox Automata: Processing paradoxes through drainage.
    This file defines a finite automaton that reads paradox symbols
    and determines how they "drain" to omega_veil or remain in Alpha.
    
    Core Insight:
    Alpha doesn't get "built up" - it's what remains when contradictions
    drain away to omega_veil. The automaton implements this drainage process,
    reading paradox patterns and determining what stays consistent vs what drains.
    
    This connects to:
    - The Restriction functor R : PRED_Omega → PRED_Alpha (drainage)
    - The monad M = R ∘ C (complete then drain)
    - Thermodynamics (entropy = accumulated drainage)
    - The arrow of time (direction of drainage)
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Lia.
Import ListNotations.

Module ParadoxAutomaton.
  

  (* ================================================================ *)
  (** ** Part I: The Alphabet - What We Read *)
  (* ================================================================ *)
  
  (** Paradox symbols are the atomic units the automaton processes.
      Each symbol carries intensional information about HOW something
      is impossible, even though extensionally they all equal omega_veil. *)
  
  Section ParadoxAlphabet.
    
    (** The symbols our automaton reads *)
    Inductive ParadoxSymbol : Type :=
      (* Primitive impossibilities *)
      | Sym_Veil : ParadoxSymbol                      (* omega_veil itself *)
      | Sym_SelfNeq : ParadoxSymbol                   (* x ≠ x pattern *)
      | Sym_Contradiction : ParadoxSymbol             (* P ∧ ¬P *)
      
      (* Arithmetic impossibilities *)
      | Sym_DivZero : nat -> ParadoxSymbol            (* n/0 *)
      | Sym_SqrtNeg : nat -> ParadoxSymbol            (* √(-n) *)
      
      (* Logical paradoxes *)
      | Sym_Russell : ParadoxSymbol                   (* Russell's paradox *)
      | Sym_Liar : ParadoxSymbol                      (* Liar paradox *)
      | Sym_Curry : ParadoxSymbol                     (* Curry's paradox *)
      
      (* Composite patterns *)
      | Sym_Compose : ParadoxSymbol -> ParadoxSymbol -> ParadoxSymbol
      | Sym_Iterate : nat -> ParadoxSymbol -> ParadoxSymbol
      
      (* Consistent content - not a paradox! *)
      | Sym_Consistent : nat -> ParadoxSymbol.        (* Actual Alpha content *)
    
    (** Classification: Does this symbol represent impossibility? *)
    Fixpoint is_impossible_symbol (s : ParadoxSymbol) : bool :=
      match s with
      | Sym_Consistent _ => false
      | Sym_Compose s1 s2 => is_impossible_symbol s1 || is_impossible_symbol s2
      | Sym_Iterate n s' => is_impossible_symbol s'
      | _ => true
      end.
    
    (** Depth of a symbol - how nested is the impossibility? *)
    Fixpoint symbol_depth (s : ParadoxSymbol) : nat :=
      match s with
      | Sym_Veil => 1
      | Sym_SelfNeq => 1
      | Sym_Contradiction => 1
      | Sym_DivZero _ => 1
      | Sym_SqrtNeg _ => 1
      | Sym_Russell => 2        (* Self-reference adds depth *)
      | Sym_Liar => 2
      | Sym_Curry => 2
      | Sym_Compose s1 s2 => symbol_depth s1 + symbol_depth s2
      | Sym_Iterate n s' => n * symbol_depth s'
      | Sym_Consistent _ => 0   (* Consistent content has no paradox depth *)
      end.
    
    (** Consistent symbols have depth 0 *)
    Lemma consistent_depth_zero : forall n,
      symbol_depth (Sym_Consistent n) = 0.
    Proof.
      intro n. reflexivity.
    Qed.
    
    (** Primitive impossible symbols have positive depth *)
    Lemma primitive_impossible_positive_depth : forall s,
      match s with
      | Sym_Veil | Sym_SelfNeq | Sym_Contradiction 
      | Sym_DivZero _ | Sym_SqrtNeg _
      | Sym_Russell | Sym_Liar | Sym_Curry => True
      | _ => False
      end ->
      symbol_depth s > 0.
    Proof.
      intros s Hprim.
      destruct s; simpl; try lia; contradiction.
    Qed.

    (** Depth 0 means either consistent or degenerate *)
    Lemma depth_zero_cases : forall s,
      symbol_depth s = 0 ->
      (exists n, s = Sym_Consistent n) \/
      (exists n s', s = Sym_Iterate n s' /\ (n = 0 \/ symbol_depth s' = 0)) \/
      (exists s1 s2, s = Sym_Compose s1 s2 /\ symbol_depth s1 = 0 /\ symbol_depth s2 = 0).
    Proof.
      intros s Hdepth.
      destruct s; simpl in Hdepth; try lia.
      - (* Sym_Compose *)
        right. right.
        exists s1, s2.
        split; [reflexivity |].
        lia.
      - (* Sym_Iterate *)
        right. left.
        destruct n.
        + exists 0, s. split; [reflexivity | left; reflexivity].
        + exists (S n), s.
          split; [reflexivity |].
          right.
          (* From Hdepth: S n * symbol_depth s = 0, and S n > 0, so symbol_depth s = 0 *)
          destruct (symbol_depth s) eqn:Hs.
          * reflexivity.
          * simpl in Hdepth. lia.
      - (* Sym_Consistent *)
        left. exists n. reflexivity.
    Qed.
      
    End ParadoxAlphabet.
    
    (* ================================================================ *)
    (** ** Part II: Drainage Results - Where Things Go *)
    (* ================================================================ *)
    
    Section DrainageResults.
      Context {Alpha : AlphaType}.
      
      (** The result of processing a symbol *)
      Inductive DrainageResult : Type :=
        | Drains : DrainageResult
            (* → omega_veil: This contradiction drains away *)
        | Stays : (Alphacarrier -> Prop) -> DrainageResult
            (* → Alpha: This content remains consistent *)
        | NeedsContext : DrainageResult.
            (* Undetermined: Need more information to decide *)
      
      (** Drainage is decidable for simple symbols *)
      Definition drain_simple (s : ParadoxSymbol) : DrainageResult :=
        match s with
        | Sym_Consistent n => Stays (fun _ => True)  (* Stays in Alpha *)
        | Sym_Veil => Drains
        | Sym_SelfNeq => Drains
        | Sym_Contradiction => Drains
        | Sym_DivZero _ => Drains
        | Sym_SqrtNeg _ => Drains
        | Sym_Russell => Drains
        | Sym_Liar => Drains
        | Sym_Curry => Drains
        | Sym_Compose _ _ => NeedsContext  (* Composite needs analysis *)
        | Sym_Iterate _ _ => NeedsContext  (* Iteration needs analysis *)
        end.
      
      (** All impossible symbols eventually drain *)
      Theorem impossible_eventually_drains :
        forall s : ParadoxSymbol,
        is_impossible_symbol s = true ->
        drain_simple s = Drains \/ drain_simple s = NeedsContext.
      Proof.
        intros s Himp.
        destruct s; simpl; auto.
        (* Sym_Consistent contradicts hypothesis *)
        discriminate.
      Qed.
      
      (** Consistent symbols stay *)
      Theorem consistent_stays :
        forall n : nat,
        exists P, drain_simple (Sym_Consistent n) = Stays P.
      Proof.
        intro n.
        exists (fun _ => True).
        reflexivity.
      Qed.
      
    End DrainageResults.
    
    (* ================================================================ *)
    (** ** Part III: The Finite Paradox Automaton *)
    (* ================================================================ *)
    
    Section FiniteParadoxAutomaton.
      Context {Alpha : AlphaType}.
      
      (** Automaton states track drainage progress *)
      Inductive AutomatonState : Type :=
        | State_Initial : AutomatonState
            (* Starting state - ready to process *)
        | State_Accumulating : nat -> AutomatonState
            (* Accumulating consistent content, tracking amount *)
        | State_Draining : nat -> AutomatonState
            (* Processing drainage, tracking depth *)
        | State_Halted : AutomatonState.
            (* Finished processing *)
      
      (** The transition function - heart of the automaton *)
      Definition transition (st : AutomatonState) (sym : ParadoxSymbol) 
        : AutomatonState * DrainageResult (Alpha := Alpha) :=
        match st with
        | State_Initial =>
            match drain_simple sym with
            | Drains => (State_Draining (symbol_depth sym), Drains)
            | Stays P => (State_Accumulating 1, Stays P)
            | NeedsContext => (State_Draining (symbol_depth sym), NeedsContext)
            end
            
        | State_Accumulating n =>
            match drain_simple sym with
            | Drains => (State_Draining (symbol_depth sym), Drains)
            | Stays P => (State_Accumulating (S n), Stays P)
            | NeedsContext => (State_Draining (symbol_depth sym), NeedsContext)
            end
            
        | State_Draining depth =>
            (* Once draining, we track how much drains *)
            match drain_simple sym with
            | Drains => (State_Draining (depth + symbol_depth sym), Drains)
            | Stays P => (State_Accumulating 1, Stays P)  (* Can recover! *)
            | NeedsContext => (State_Draining (depth + symbol_depth sym), NeedsContext)
            end
            
        | State_Halted =>
            (* Halted state ignores input *)
            (State_Halted, Drains)
        end.
      
      (** The complete automaton structure *)
      Record ParadoxFA := {
        fa_state : AutomatonState;
        fa_drained : nat;        (* Total depth drained to omega_veil *)
        fa_accumulated : nat;    (* Consistent content accumulated *)
        fa_history : list ParadoxSymbol  (* What we've processed *)
      }.
      
      (** Initial automaton *)
      Definition initial_fa : ParadoxFA := {|
        fa_state := State_Initial;
        fa_drained := 0;
        fa_accumulated := 0;
        fa_history := []
      |}.
      
      (** Step the automaton forward *)
      Definition step_fa (fa : ParadoxFA) (sym : ParadoxSymbol) : ParadoxFA :=
        let (new_state, result) := transition (fa_state fa) sym in
        {|
          fa_state := new_state;
          fa_drained := 
            match result with
            | Drains => fa_drained fa + symbol_depth sym
            | _ => fa_drained fa
            end;
          fa_accumulated :=
            match result with
            | Stays _ => S (fa_accumulated fa)
            | _ => fa_accumulated fa
            end;
          fa_history := sym :: fa_history fa
        |}.
      
      (** Run the automaton on a list of symbols *)
      Fixpoint run_fa (fa : ParadoxFA) (input : list ParadoxSymbol) : ParadoxFA :=
        match input with
        | [] => fa
        | sym :: rest => run_fa (step_fa fa sym) rest
        end.
      
      (** Process input from initial state *)
      Definition process (input : list ParadoxSymbol) : ParadoxFA :=
        run_fa initial_fa input.
      
    End FiniteParadoxAutomaton.
    
    (* ================================================================ *)
    (** ** Part IV: Properties of the Automaton *)
    (* ================================================================ *)
    
    Section AutomatonProperties.
      Context {Alpha : AlphaType}.
      
      (** Drainage is monotonic - once drained, always drained *)
      Theorem drainage_monotonic :
        forall (fa : ParadoxFA) (sym : ParadoxSymbol),
        fa_drained fa <= fa_drained (step_fa fa sym).
      Proof.
        intros fa sym.
        unfold step_fa.
        destruct (transition (fa_state fa) sym) as [new_state result].
        simpl.
        destruct result; lia.
      Qed.
      
      (** Running more input only increases drainage *)
      Theorem run_increases_drainage :
        forall (fa : ParadoxFA) (input : list ParadoxSymbol),
        fa_drained fa <= fa_drained (run_fa fa input).
      Proof.
        intros fa input.
        generalize dependent fa.
        induction input as [| sym rest IH]; intro fa.
        - simpl. lia.
        - simpl.
          transitivity (fa_drained (step_fa fa sym)).
          + apply drainage_monotonic.
          + apply IH.
      Qed.
      
      (** All-impossible input results in all-drainage *)
      Theorem all_impossible_all_drains :
        forall (input : list ParadoxSymbol),
        Forall (fun s => is_impossible_symbol s = true) input ->
        Forall (fun s => drain_simple (Alpha := Alpha) s <> Stays (fun _ => True)) input ->
        fa_accumulated (process (Alpha := Alpha) input) = 0.
      Proof.
        intros input Hall Hdrains.
        unfold process.
        induction input as [| sym rest IH].
        - simpl. reflexivity.
        - simpl.
          (* This needs more careful analysis of the state transitions *)
          (* For now, we note the structure *)
      Admitted.
      
      (** Conservation law: total = drained + accumulated (modulo depth) *)
      Theorem drainage_conservation :
        forall (input : list ParadoxSymbol),
        let fa := process (Alpha := Alpha) input in
        fa_drained fa + fa_accumulated fa >= length input.
      Proof.
        intro input.
        unfold process.
        induction input as [| sym rest IH].
        - simpl. lia.
        - simpl.
          (* Step adds to either drained or accumulated *)
      Admitted.
      
    End AutomatonProperties.
    
    (* ================================================================ *)
    (** ** Part V: Connection to the Monad *)
    (* ================================================================ *)

    (** The automaton implements the monad M = R ∘ C operationally.
        
        - Reading a symbol = applying C (completion) to get Omega view
        - Transition function = applying R (restriction) to drain
        - Final state = the Alpha content that remains
    *)

    Section MonadConnection.
      Context {Alpha : AlphaType}.
      Context {Omega : OmegaType}.
      Context (embed : Alphacarrier -> Omegacarrier).
      
      (** Symbols can be lifted to Omega predicates *)
      Definition symbol_to_omega_pred (sym : ParadoxSymbol) : Omegacarrier -> Prop :=
        fun _ =>
          match sym with
          | Sym_Consistent _ => True
          | _ => False  (* Impossible symbols represent omega_veil witnesses *)
          end.
      
      (** The automaton's drainage corresponds to restriction *)
      (** When a symbol drains, it means the corresponding Omega predicate
          restricts to omega_veil in Alpha (nothing consistent remains) *)
      Definition drainage_is_restriction :
        forall (sym : ParadoxSymbol),
        drain_simple (Alpha := Alpha) sym = Drains ->
        forall a : Alphacarrier, 
          symbol_to_omega_pred sym (embed a) = False \/ omega_veil a.
      Proof.
        intros sym Hdrain a.
        destruct sym; simpl in Hdrain; try discriminate; simpl; auto.
      Qed.
      
      (** The key correspondence: automaton run ≈ monad bind *)
      (** 
          run_fa fa [s1; s2; s3] 
          ≈ 
          bind (process s3) (bind (process s2) (bind (process s1) return))
          
          This is a conceptual correspondence - full proof would require
          connecting ParadoxFA states to the categorical monad structure.
      *)
      
    End MonadConnection.
    
    (* ================================================================ *)
    (** ** Part VI: Entropy and Time *)
    (* ================================================================ *)
    
    (** The automaton reveals thermodynamic structure:
        - Drainage = entropy increase
        - fa_drained = accumulated entropy
        - Time = sequence of transitions
        - Arrow of time = drainage direction
    *)
    
    Section ThermodynamicStructure.
      Context {Alpha : AlphaType}.
      
      (** Entropy is the drainage count *)
      Definition entropy (fa : ParadoxFA) : nat :=
        fa_drained fa.
      
      (** Entropy never decreases (Second Law) *)
      Theorem second_law :
        forall (fa : ParadoxFA) (sym : ParadoxSymbol),
        entropy fa <= entropy (step_fa fa sym).
      Proof.
        intros fa sym.
        unfold entropy.
        apply drainage_monotonic.
      Qed.
      
      (** Entropy increase defines time direction *)
      Definition time_order (fa1 fa2 : ParadoxFA) : Prop :=
        entropy fa1 <= entropy fa2.
      
      (** Time order is transitive *)
      Theorem time_transitive :
        forall fa1 fa2 fa3 : ParadoxFA,
        time_order fa1 fa2 -> time_order fa2 fa3 -> time_order fa1 fa3.
      Proof.
        unfold time_order. intros. lia.
      Qed.
      
      (** Processing creates time flow *)
      Theorem processing_creates_time :
        forall (fa : ParadoxFA) (input : list ParadoxSymbol),
        input <> [] ->
        Exists (fun s => is_impossible_symbol s = true) input ->
        time_order fa (run_fa fa input).
      Proof.
        intros fa input Hne Hex.
        unfold time_order, entropy.
        apply run_increases_drainage.
      Qed.
      
    End ThermodynamicStructure.
    
    (* ================================================================ *)
    (** ** Part VII: Examples *)
    (* ================================================================ *)
    
    Section Examples.
      Context {Alpha : AlphaType}.
      
      (** Example 1: Pure paradox input - all drains *)
      Example pure_paradox :
        let input := [Sym_Russell; Sym_Liar; Sym_Contradiction] in
        let fa := process (Alpha := Alpha) input in
        fa_drained fa = 5 /\  (* 2 + 2 + 1 *)
        fa_accumulated fa = 0.
      Proof.
        simpl.
        split; reflexivity.
      Qed.
      
      (** Example 2: Pure consistent input - all stays *)
      Example pure_consistent :
        let input := [Sym_Consistent 1; Sym_Consistent 2; Sym_Consistent 3] in
        let fa := process (Alpha := Alpha) input in
        fa_drained fa = 0 /\
        fa_accumulated fa = 3.
      Proof.
        simpl.
        split; reflexivity.
      Qed.
      
      (** Example 3: Mixed input - partial drainage *)
      Example mixed_input :
        let input := [Sym_Consistent 1; Sym_Russell; Sym_Consistent 2] in
        let fa := process (Alpha := Alpha) input in
        fa_drained fa = 2 /\      (* Just Russell drains *)
        fa_accumulated fa = 2.    (* Two consistent symbols stay *)
      Proof.
        simpl.
        split; reflexivity.
      Qed.
      
      (** Example 4: Entropy increases with paradox depth *)
      Example entropy_from_depth :
        let shallow := [Sym_Contradiction] in  (* depth 1 *)
        let deep := [Sym_Russell] in           (* depth 2 *)
        entropy (process (Alpha := Alpha) shallow) < 
        entropy (process (Alpha := Alpha) deep).
      Proof.
        simpl. lia.
      Qed.
      
      (** Example 5: Division by zero drains *)
      Example div_zero_drains :
        let input := [Sym_DivZero 1; Sym_DivZero 2; Sym_DivZero 42] in
        let fa := process (Alpha := Alpha) input in
        fa_accumulated fa = 0.  (* Nothing stays - all drain to omega_veil *)
      Proof.
        simpl. reflexivity.
      Qed.
      
    End Examples.
    
    (* ================================================================ *)
    (** ** Part VIII: Dual Tape Automaton (Preview) *)
    (* ================================================================ *)
    
    (** For dual Alpha projections, we'd need two output tapes.
        This sketches the structure - full development would go in
        a separate file. *)
    
    Section DualTapeSketch.
      
      (** Dual drainage result *)
      Inductive DualDrainageResult : Type :=
        | Drains_Both : DualDrainageResult
            (* Drains to omega_veil - neither Alpha sees it *)
        | Stays_Positive : DualDrainageResult
            (* Goes to Alpha+ *)
        | Stays_Negative : DualDrainageResult
            (* Goes to Alpha- *)
        | Splits : DualDrainageResult.
            (* Content appears in both (rare/special case) *)
      
      (** A dual automaton would have:
          - Input tape: ParadoxSymbols
          - Positive output tape: Alpha+ content
          - Negative output tape: Alpha- content
          - Drainage counter: What went to omega_veil
          
          The separator function determines positive vs negative.
      *)
      
      Record DualParadoxFA := {
        dual_state : AutomatonState;
        dual_drained : nat;
        dual_positive : nat;   (* Content in Alpha+ *)
        dual_negative : nat;   (* Content in Alpha- *)
        dual_history : list ParadoxSymbol
      }.
      
      (** The key insight: Alpha+ and Alpha- together exhaust 
          the non-drainage options. What doesn't drain goes to
          exactly one of them (by the partition theorem). *)
      
    End DualTapeSketch.

    (* ================================================================ *)
    (** ** Part IX: Dual Tape Automaton *)
    (* ================================================================ *)

    (** Full development of the dual tape automaton that splits
        Omega content into Alpha+ and Alpha- projections.
        
        This connects to ExistenceAdjunction.DualAlphas:
        - separator determines which Alpha receives consistent content
        - Contradictions drain to omega_veil (neither Alpha sees them)
        - Alpha+ and Alpha- together partition the non-drained content
    *)

    Section DualTapeAutomaton.
      Context {Omega : OmegaType}.
      
      (** The separator function determines the split *)
      Variable separator : Omegacarrier -> bool.
      
      (** We need witnesses for both projections to be non-empty *)
      Variable positive_witness : { x : Omegacarrier | separator x = false }.
      Variable negative_witness : { x : Omegacarrier | separator x = true }.
      
      (** Import the dual Alpha types from our construction *)
      (** In a real development, these would come from ExistenceAdjunction *)
      
      Let Alpha_pos : Type := { x : Omegacarrier | separator x = false }.
      Let Alpha_neg : Type := { x : Omegacarrier | separator x = true }.
      
      (** Dual drainage: where does each symbol go? *)
      Inductive DualDrainResult : Type :=
        | DDrain : DualDrainResult                     (* → omega_veil *)
        | DStay_Pos : (Alpha_pos -> Prop) -> DualDrainResult  (* → Alpha+ *)
        | DStay_Neg : (Alpha_neg -> Prop) -> DualDrainResult  (* → Alpha- *)
        | DNeedsRouting : DualDrainResult.             (* Consistent but needs separator *)
      
      (** First pass: determine if symbol drains or stays *)
      Definition dual_drain_phase1 (s : ParadoxSymbol) : DualDrainResult :=
        match s with
        | Sym_Consistent _ => DNeedsRouting  (* Stays, but where? *)
        | Sym_Veil => DDrain
        | Sym_SelfNeq => DDrain
        | Sym_Contradiction => DDrain
        | Sym_DivZero _ => DDrain
        | Sym_SqrtNeg _ => DDrain
        | Sym_Russell => DDrain
        | Sym_Liar => DDrain
        | Sym_Curry => DDrain
        | Sym_Compose _ _ => DDrain  (* Simplification: composites drain *)
        | Sym_Iterate _ _ => DDrain  (* Simplification: iterations drain *)
        end.
      
      (** Second pass: route consistent content using separator *)
      (** In a full implementation, we'd need to associate Omega elements
          with symbols. For now, we use a routing decision. *)
      Definition route_consistent (routing_bit : bool) : DualDrainResult :=
        match routing_bit with
        | false => DStay_Pos (fun _ => True)
        | true => DStay_Neg (fun _ => True)
        end.
      
      (** Combined drainage with routing *)
      Definition dual_drain (s : ParadoxSymbol) (routing : bool) : DualDrainResult :=
        match dual_drain_phase1 s with
        | DNeedsRouting => route_consistent routing
        | other => other
        end.
      
      (** The dual automaton state *)
      Record DualFA := {
        dfa_state : AutomatonState;
        dfa_drained : nat;       (* Entropy: what went to omega_veil *)
        dfa_pos_count : nat;     (* Content routed to Alpha+ *)
        dfa_neg_count : nat;     (* Content routed to Alpha- *)
        dfa_history : list (ParadoxSymbol * bool)  (* Symbol and routing bit *)
      }.
      
      (** Initial dual automaton *)
      Definition initial_dfa : DualFA := {|
        dfa_state := State_Initial;
        dfa_drained := 0;
        dfa_pos_count := 0;
        dfa_neg_count := 0;
        dfa_history := []
      |}.
      
      (** Step the dual automaton *)
      Definition step_dfa (dfa : DualFA) (sym : ParadoxSymbol) (routing : bool) : DualFA :=
        let result := dual_drain sym routing in
        {|
          dfa_state := 
            match result with
            | DDrain => State_Draining (symbol_depth sym)
            | DStay_Pos _ => State_Accumulating 1
            | DStay_Neg _ => State_Accumulating 1
            | DNeedsRouting => dfa_state dfa  (* Shouldn't happen after dual_drain *)
            end;
          dfa_drained :=
            match result with
            | DDrain => dfa_drained dfa + symbol_depth sym
            | _ => dfa_drained dfa
            end;
          dfa_pos_count :=
            match result with
            | DStay_Pos _ => S (dfa_pos_count dfa)
            | _ => dfa_pos_count dfa
            end;
          dfa_neg_count :=
            match result with
            | DStay_Neg _ => S (dfa_neg_count dfa)
            | _ => dfa_neg_count dfa
            end;
          dfa_history := (sym, routing) :: dfa_history dfa
        |}.
      
      (** Run on a list of (symbol, routing) pairs *)
      Fixpoint run_dfa (dfa : DualFA) (input : list (ParadoxSymbol * bool)) : DualFA :=
        match input with
        | [] => dfa
        | (sym, routing) :: rest => run_dfa (step_dfa dfa sym routing) rest
        end.
      
      (** Process from initial state *)
      Definition process_dual (input : list (ParadoxSymbol * bool)) : DualFA :=
        run_dfa initial_dfa input.
      
      (* -------------------------------------------------------------- *)
      (** *** Properties of the Dual Automaton *)
      (* -------------------------------------------------------------- *)
      
      (** Drainage is still monotonic *)
      Theorem dual_drainage_monotonic :
        forall (dfa : DualFA) (sym : ParadoxSymbol) (routing : bool),
        dfa_drained dfa <= dfa_drained (step_dfa dfa sym routing).
      Proof.
        intros dfa sym routing.
        unfold step_dfa.
        destruct (dual_drain sym routing); simpl; lia.
      Qed.
      
      (** The partition property: non-drained content goes to exactly one Alpha *)
      Theorem partition_property :
        forall (sym : ParadoxSymbol) (routing : bool),
        let result := dual_drain sym routing in
        match result with
        | DDrain => True  (* Drained - neither Alpha *)
        | DStay_Pos _ => True  (* Goes to Alpha+ only *)
        | DStay_Neg _ => True  (* Goes to Alpha- only *)
        | DNeedsRouting => False  (* Should never happen *)
        end.
      Proof.
        intros sym routing.
        unfold dual_drain.
        destruct (dual_drain_phase1 sym) eqn:Hphase1; simpl; auto.
        (* DNeedsRouting case: route_consistent always gives DStay_Pos or DStay_Neg *)
        unfold route_consistent.
        destruct routing; auto.
      Qed.
      
      (** Exclusivity: content never goes to both Alphas *)
      Theorem dual_exclusivity :
        forall (dfa : DualFA) (sym : ParadoxSymbol) (routing : bool),
        let dfa' := step_dfa dfa sym routing in
        (* At most one counter increases *)
        (dfa_pos_count dfa' = S (dfa_pos_count dfa) -> 
        dfa_neg_count dfa' = dfa_neg_count dfa) /\
        (dfa_neg_count dfa' = S (dfa_neg_count dfa) -> 
        dfa_pos_count dfa' = dfa_pos_count dfa).
      Proof.
        intros dfa sym routing.
        unfold step_dfa.
        destruct (dual_drain sym routing) eqn:Hresult; simpl.
        - (* DDrain - neither counter increases, so premises are false *)
          split; intro H; lia.
        - (* DStay_Pos - pos increases, neg stays same *)
          split; intro H.
          + reflexivity.
          + lia.  (* Premise dfa_neg_count dfa = S (dfa_neg_count dfa) is false *)
        - (* DStay_Neg - neg increases, pos stays same *)
          split; intro H.
          + lia.  (* Premise dfa_pos_count dfa = S (dfa_pos_count dfa) is false *)
          + reflexivity.
        - (* DNeedsRouting - neither counter increases *)
          split; intro H; lia.
      Qed.
      
      (** Conservation: every symbol either drains or goes to an Alpha *)
      (** Note: zero-depth drains are an edge case that don't increase counters *)
      Theorem dual_conservation :
        forall (dfa : DualFA) (sym : ParadoxSymbol) (routing : bool),
        let dfa' := step_dfa dfa sym routing in
        (* Something changes - or it's a zero-depth drain *)
        (dfa_drained dfa' > dfa_drained dfa) \/
        (dfa_pos_count dfa' > dfa_pos_count dfa) \/
        (dfa_neg_count dfa' > dfa_neg_count dfa) \/
        (dual_drain sym routing = DDrain /\ symbol_depth sym = 0).
      Proof.
        intros dfa sym routing.
        unfold step_dfa.
        destruct (dual_drain sym routing) eqn:Hresult; simpl.
        - (* DDrain *)
          destruct (symbol_depth sym) eqn:Hdepth.
          + (* depth = 0: edge case *)
            right. right. right. auto.
          + (* depth > 0: drainage increases *)
            left. lia.
        - (* DStay_Pos *)
          right. left. lia.
        - (* DStay_Neg *)
          right. right. left. lia.
        - (* DNeedsRouting - show this can't happen *)
          unfold dual_drain in Hresult.
          destruct (dual_drain_phase1 sym); try discriminate.
          unfold route_consistent in Hresult.
          destruct routing; discriminate.
      Qed.
      
      (* -------------------------------------------------------------- *)
      (** *** Examples *)
      (* -------------------------------------------------------------- *)
      
      (** Example: Paradoxes drain, consistent content splits *)
      Example dual_mixed_example :
        let input := [(Sym_Consistent 1, false);   (* → Alpha+ *)
                      (Sym_Russell, false);        (* → drains *)
                      (Sym_Consistent 2, true);    (* → Alpha- *)
                      (Sym_Consistent 3, false)]   (* → Alpha+ *)
        in
        let dfa := process_dual input in
        dfa_drained dfa = 2 /\      (* Russell's depth *)
        dfa_pos_count dfa = 2 /\    (* Two to Alpha+ *)
        dfa_neg_count dfa = 1.      (* One to Alpha- *)
      Proof.
        simpl.
        repeat split; reflexivity.
      Qed.
      
      (** Example: All paradoxes → all drain, nothing to either Alpha *)
      Example dual_all_paradox :
        let input := [(Sym_Liar, false); (Sym_Curry, true); (Sym_Veil, false)] in
        let dfa := process_dual input in
        dfa_drained dfa = 5 /\      (* 2 + 2 + 1 *)
        dfa_pos_count dfa = 0 /\
        dfa_neg_count dfa = 0.
      Proof.
        simpl.
        repeat split; reflexivity.
      Qed.
      
      (** Example: Routing bit determines destination for consistent content *)
      Example routing_determines_destination :
        let same_symbol := Sym_Consistent 42 in
        let to_pos := process_dual [(same_symbol, false)] in
        let to_neg := process_dual [(same_symbol, true)] in
        dfa_pos_count to_pos = 1 /\ dfa_neg_count to_pos = 0 /\
        dfa_pos_count to_neg = 0 /\ dfa_neg_count to_neg = 1.
      Proof.
        simpl.
        repeat split; reflexivity.
      Qed.

    End DualTapeAutomaton.

End ParadoxAutomaton.

(** 
  Summary:
  
  We've built a finite paradox automaton that implements the drainage
  process from Omega to Alpha. Key features:
  
  1. ALPHABET: Paradox symbols carry intensional information about 
     different kinds of impossibility
  
  2. DRAINAGE: The automaton processes symbols and determines what
     drains to omega_veil vs what stays as consistent Alpha content
  
  3. MONOTONICITY: Once something drains, it stays drained (entropy
     never decreases)
  
  4. THERMODYNAMICS: fa_drained tracks entropy; processing paradoxes
     increases entropy and defines the arrow of time
  
  5. MONAD CONNECTION: The automaton operationally implements the
     monad M = R ∘ C from the adjunction
  
  Next steps:
  - Prove stronger correspondence with the categorical monad
  - Develop the dual tape automaton for Alpha± projections  
  - Connect to the Halting problem via undecidable drainage
  - Explore infinite input streams (ω-automata)
*)