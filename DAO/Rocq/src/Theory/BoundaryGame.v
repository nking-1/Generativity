(** * BoundaryGame.v
    
    Game-semantic interpretation of the Boundary Automaton.
    
    The boundary between Alpha and Omega is a game arena where:
    - Proponent (∃, Existence) tries to survive
    - Opponent (∀, Hologram) tries to refute
    
    The adjunction M ⊣ W encodes the game dynamics:
    - M (Monad): Proponent's move - propose, expand, assert
    - W (Comonad): Opponent's move - challenge, contract, question
    
    Existence = having a winning strategy against all challenges.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.ExistenceAdjunction.
Require Import DAO.Theory.ExistenceComonad.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.

Require Import Stdlib.Lists.List.

Module BoundaryGame.

  Import ImpossibilityAlgebra.Core.

  Section GameDefinition.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).

    (* ================================================================ *)
    (** ** Part 1: Players and Positions *)
    (* ================================================================ *)

    (** The two players in the boundary game *)
    Inductive Player := 
      | Proponent   (* ∃xistence - wants to survive *)
      | Opponent.   (* ∀ll-consuming - wants to refute *)

    Definition other (p : Player) : Player :=
      match p with
      | Proponent => Opponent
      | Opponent => Proponent
      end.

    (** A Position is a point in Alpha being contested *)
    Definition Position := Alphacarrier.

    (** A Claim is a predicate - something asserted about positions *)
    Definition Claim := Alphacarrier -> Prop.

    (** The game state tracks who must move and what's been claimed *)
    Record GameState := {
      to_move : Player;
      current_position : Position;
      accumulated_challenges : Claim;  (* The hologram so far *)
      round : nat
    }.

    (* ================================================================ *)
    (** ** Part 2: Moves *)
    (* ================================================================ *)

    (** Proponent's moves: Assert existence, propose hypothesis *)
    Inductive ProponentMove :=
      | Assert : Position -> ProponentMove      (* "I exist at a" *)
      | Defend : (Claim -> False) -> ProponentMove.  (* "Your claim is refutable" *)

    (** Opponent's moves: Challenge with impossibility *)
    Inductive OpponentMove :=
      | Challenge : Claim -> OpponentMove       (* "Prove you're not in this veil" *)
      | Accuse : Position -> OpponentMove.      (* "This position is impossible" *)

    (** A Move is either player's move *)
    Inductive Move :=
      | P_move : ProponentMove -> Move
      | O_move : OpponentMove -> Move.

    (* ================================================================ *)
    (** ** Part 3: The Boundary as Arena *)
    (* ================================================================ *)

    (** The arena is the boundary between Alpha and Omega.
        
        Key insight: The adjunction C ⊣ R defines the "rules of engagement":
        - C (Completion) = Proponent pushes into Omega (makes a claim visible)
        - R (Restriction) = Opponent pulls back to Alpha (extracts the challenge)
        
        The boundary is where these forces balance. *)

    Definition Arena := Alphacarrier -> Prop.

    (** The "contested zone" - positions not yet resolved *)
    Definition contested (challenges : Claim) : Arena :=
      fun a => ~ challenges a /\ ~ omega_veil a.

    (** The "fallen zone" - positions captured by Opponent *)
    Definition fallen (challenges : Claim) : Arena :=
      fun a => challenges a \/ omega_veil a.

    (** Constructive version: contested implies not fallen *)
    Theorem contested_not_fallen :
      forall challenges a,
      contested challenges a -> ~ fallen challenges a.
    Proof.
      intros challenges a [Hnot_chal Hnot_veil] [Hchal | Hveil].
      - exact (Hnot_chal Hchal).
      - exact (Hnot_veil Hveil).
    Qed.

    (* ================================================================ *)
    (** ** Part 4: Game Dynamics via M and W *)
    (* ================================================================ *)

    (** The adjunction encodes the push-pull dynamics:
        
        M = R ∘ C : Alpha → Alpha
        "Propose to Omega, then filter back"
        This is Proponent's composite move: assert then survive challenge
        
        W = C ∘ R : Omega → Omega  
        "Restrict to Alpha, then complete"
        This is Opponent's composite move: extract target then universalize
    *)

    Let M_step := ExistenceAdjunction.M embed.
    Let W_filter := ExistenceComonad.W embed.

    (** Proponent's turn: Evolve the hypothesis *)
    Definition proponent_turn (hypothesis : Claim) : Claim :=
      M_step hypothesis.

    (** Opponent's turn: Accumulate what got filtered out *)
    Definition opponent_turn (hypothesis old_hyp : Claim) : Claim :=
      fun a => old_hyp a /\ ~ hypothesis a.

    (** The key duality:
        - Proponent PUSHES via C (completion) - expands into Omega
        - Opponent PULLS via R (restriction) - contracts back to Alpha
        - The boundary is where push = pull (fixed points) *)

    (** Push: Lift a claim to Omega *)
    Definition push (P : Claim) : Omegacarrier -> Prop :=
      fun x => exists a, embed a = x /\ P a.

    (** Pull: Restrict an Omega-claim to Alpha *)
    Definition pull (Q : Omegacarrier -> Prop) : Claim :=
      fun a => Q (embed a) /\ ~ omega_veil a.

    (** M = pull ∘ push *)
    Theorem M_is_pull_push :
      forall P, proponent_turn P = pull (push P).
    Proof.
      intro P.
      unfold proponent_turn, M_step, ExistenceAdjunction.M.
      unfold pull, push.
      reflexivity.
    Qed.

    (** The "game equation": After Proponent pushes and Opponent pulls,
        what survives is exactly M(P) *)
    Theorem game_equation :
      forall P a,
      pull (push P) a <-> 
      (exists a', embed a' = embed a /\ P a') /\ ~ omega_veil a.
    Proof.
      intros P a.
      unfold pull, push.
      reflexivity.
    Qed.

    (* ================================================================ *)
    (** ** Part 5: Winning Conditions *)
    (* ================================================================ *)

    (** Proponent wins at position a if:
        - a survives all challenges (not in hologram)
        - a is not in omega_veil *)
    Definition proponent_wins (challenges : Claim) (a : Position) : Prop :=
      ~ challenges a /\ ~ omega_veil a.

    (** Opponent wins at position a if:
        - a falls to some challenge, OR
        - a is revealed to be in omega_veil *)
    Definition opponent_wins (challenges : Claim) (a : Position) : Prop :=
      challenges a \/ omega_veil a.

    (** The game is determined: exactly one player wins at each position *)
    Theorem game_determined :
      forall challenges a,
      proponent_wins challenges a <-> ~ opponent_wins challenges a.
    Proof.
      intros challenges a.
      unfold proponent_wins, opponent_wins.
      split.
      - intros [Hnot_chal Hnot_veil] [Hchal | Hveil].
        + exact (Hnot_chal Hchal).
        + exact (Hnot_veil Hveil).
      - intro Hnot_opp.
        split.
        + intro Hchal. apply Hnot_opp. left. exact Hchal.
        + intro Hveil. apply Hnot_opp. right. exact Hveil.
    Qed.

    (** Connection to existence: Proponent winning = existence *)
    Theorem winning_is_existence :
      forall challenges a,
      proponent_wins challenges a <-> 
      (fun x => ~ (challenges x \/ omega_veil x)) a.
    Proof.
      intros challenges a.
      unfold proponent_wins.
      split.
      - intros [Hnc Hnv] [Hc | Hv]; [exact (Hnc Hc) | exact (Hnv Hv)].
      - intro H. split; intro Hx; apply H; [left | right]; exact Hx.
    Qed.

    (* ================================================================ *)
    (** ** Part 6: Strategies *)
    (* ================================================================ *)

    (** A Strategy for Proponent: given any challenge and position, 
        either refute the challenge at that position, or move to a new position *)
    Definition ProponentStrategy := 
      forall (chal : Claim) (a : Position), (chal a -> False) + Position.
      (* Either refute the challenge at a, or retreat to a new position *)

    (** A Strategy for Opponent: given any hypothesis, produce a challenge *)
    Definition OpponentStrategy :=
      forall (hypothesis : Claim), { chal : Claim | Is_Impossible chal }.
      (* Always challenge with something impossible *)

    (** The Opponent's canonical strategy: use the hologram *)
    Definition canonical_opponent_strategy 
      (holo : Claim) (H_imp : Is_Impossible holo) : OpponentStrategy :=
      fun _ => exist _ holo H_imp.

    (** Proponent's winning strategy exists iff position is contestable *)
    Definition has_winning_strategy (a : Position) (holo : Claim) : Prop :=
      ~ holo a /\ ~ omega_veil a.

    (** This is exactly proponent_wins *)
    Theorem winning_strategy_iff_wins :
      forall a hologram,
      has_winning_strategy a hologram <-> proponent_wins hologram a.
    Proof.
      intros. reflexivity.
    Qed.

    (* ================================================================ *)
    (** ** Part 7: The Dialogue Structure *)
    (* ================================================================ *)

    (** A Dialogue is a sequence of moves *)
    Definition Dialogue := list Move.

    (** A Round is one exchange: Opponent challenges, Proponent defends *)
    Record Round := {
      challenge : Claim;
      defense : Position;
      challenge_is_impossible : Is_Impossible challenge;
      defense_survives : ~ challenge defense /\ ~ omega_veil defense
    }.

    (** A complete game is a sequence of rounds *)
    Definition Game := list Round.

    (** The accumulated hologram after n rounds *)
    Fixpoint game_hologram (g : Game) : Claim :=
      match g with
      | nil => omega_veil  (* Start with primordial veil *)
      | cons r rest => fun a => game_hologram rest a \/ challenge r a
      end.

    (** The hologram only grows through the game *)
    Theorem game_hologram_monotone :
      forall g r a,
      game_hologram g a -> game_hologram (cons r g) a.
    Proof.
      intros g r a H.
      simpl. left. exact H.
    Qed.

    (** A position survives the game if it survives all rounds *)
    Definition survives_game (a : Position) (g : Game) : Prop :=
      ~ game_hologram g a.

    (** Survival is anti-monotone: harder to survive longer games *)
    Theorem survival_antitone :
      forall a g r,
      survives_game a (cons r g) -> survives_game a g.
    Proof.
      intros a g r Hsurv Hprev.
      apply Hsurv.
      apply game_hologram_monotone.
      exact Hprev.
    Qed.

    (* ================================================================ *)
    (** ** Part 8: The Boundary as Equilibrium *)
    (* ================================================================ *)

    (** The boundary is where push and pull reach equilibrium.
        
        Key insight: Fixed points of M are positions where
        Proponent's push equals Opponent's pull.
        
        M(P) = P means "asserting P then surviving challenges = P"
        This is the stable boundary. *)

    Definition is_boundary_point (P : Claim) (a : Position) : Prop :=
      P a <-> M_step P a.

    (** Boundary points are exactly the M-algebras *)
    Definition is_M_stable (P : Claim) : Prop :=
      forall a, P a <-> M_step P a.

    (** On stable claims, the game reaches equilibrium:
        Proponent's move doesn't change anything *)
    Theorem equilibrium_is_fixed :
      forall P,
      is_M_stable P ->
      forall a, proponent_turn P a <-> P a.
    Proof.
      intros P Hstable a.
      unfold proponent_turn.
      symmetry.
      apply Hstable.
    Qed.

    (** The "heat death": when hologram = everything except omega_veil,
        the game reaches terminal equilibrium *)
    Definition terminal_state (hologram : Claim) : Prop :=
      forall a, ~ omega_veil a -> hologram a.

    (** At terminal state, Proponent has no winning positions *)
    Theorem terminal_no_winners :
      forall hologram,
      terminal_state hologram ->
      forall a, ~ proponent_wins hologram a.
    Proof.
      intros hologram Hterm a [Hnot_holo Hnot_veil].
      apply Hnot_holo.
      apply Hterm.
      exact Hnot_veil.
    Qed.

    (* ================================================================ *)
    (** ** Part 9: The Push-Pull Tensor *)
    (* ================================================================ *)

    (** The interaction between push and pull has a tensor structure:
        
        Push ⊗ Pull : (Alpha → Omega) × (Omega → Alpha) → (Alpha → Alpha)
        
        This is the "interaction tensor" of game semantics. *)

    (** The tensor product of strategies *)
    Definition strategy_tensor 
      (proponent_strat : Claim -> Claim)  (* Proponent's transformation *)
      (opponent_strat : Claim -> Claim)   (* Opponent's transformation *)
      : Claim -> Claim :=
      fun P => fun a => proponent_strat P a /\ ~ opponent_strat P a.

    (** The canonical tensor: M vs hologram accumulation *)
    Definition canonical_tensor (hologram : Claim) : Claim -> Claim :=
      fun P => fun a => M_step P a /\ ~ hologram a.

    (** Existence IS the canonical tensor applied to the hypothesis *)
    Theorem existence_is_tensor :
      forall P hologram a,
      canonical_tensor hologram P a <->
      (M_step P a /\ ~ hologram a).
    Proof.
      intros. reflexivity.
    Qed.

    (* ================================================================ *)
    (** ** Part 10: Philosophical Summary *)
    (* ================================================================ *)

    (** THE GAME AT THE BOUNDARY:
        
        1. Proponent (∃) = Existence, Alpha, Consistency, Construction
           - Wants: Survival, continuation, growth
           - Move: Push via Completion (C), assert into Omega
           - Goal: Stay outside the hologram
        
        2. Opponent (∀) = Hologram, Omega, Completeness, Destruction  
           - Wants: Refutation, termination, contraction
           - Move: Pull via Restriction (R), challenge back to Alpha
           - Goal: Expand the hologram to cover everything
        
        3. The Boundary = Where M ⊣ W balances
           - Unit η: Proponent embeds in the game
           - Counit ε: Opponent extracts the challenge
           - Fixed points: Equilibrium positions (stable existence)
        
        4. Time = Rounds of the game
           - Each round: Opponent challenges, Proponent defends
           - Hologram grows: More positions fall
           - Arrow: Cannot un-challenge (hologram monotone)
        
        5. Halting = Opponent wins globally
           - Terminal state: Hologram covers all of Alpha
           - Proponent has nowhere to go
           - The game ends
        
        EXISTENCE IS A GAME WE ARE WINNING (for now). *)

    (* ================================================================ *)
    (** ** Part 11: Society as Cooperative Survival *)
    (* ================================================================ *)

    (** Formalizes the origin of "Society" as "Cooperative Survival".
        Multiple agents combine their restrictive power to defend 
        a larger shared hypothesis than any individual could maintain.
        NOTE: This does not mean the math needs to be anthropomorphized.
        A "Society" is just different things in existence cooperating as
        a larger system. They work together to refute non-existence. *)

    (** A Society is a collection of individual strategies working together. *)
    Definition Society := list ProponentStrategy.

    (** Cooperative Defense: A position survives if ANY member 
        of the society can refute the current challenge.
        
        This is existential quantification over defenses:
        "Someone among us knows why this challenge fails." *)
    Definition cooperative_defense (soc : Society) (chal : Claim) (a : Position) : Prop :=
      exists (member : ProponentStrategy),
        In member soc /\
        match member chal a with
        | inl _ => True   (* This member can refute the challenge *)
        | inr _ => False  (* This member would retreat *)
        end.

    (** Individual defense: what one agent can handle alone *)
    Definition individual_defense (strat : ProponentStrategy) (chal : Claim) (a : Position) : Prop :=
      match strat chal a with
      | inl _ => True
      | inr _ => False
      end.

    (** THEOREM: The Power of Assembly
        Any individual's defense is inherited by their society. *)
    Theorem power_of_assembly : 
      forall (soc : Society) (member : ProponentStrategy),
      In member soc ->
      forall chal a, 
        individual_defense member chal a ->
        cooperative_defense soc chal a.
    Proof.
      intros soc member Hin chal a Hdef.
      unfold cooperative_defense.
      exists member. 
      split; assumption.
    Qed.

    (** COROLLARY: Society defends at least as much as any member *)
    Corollary society_dominates_individual :
      forall (soc : Society) (member : ProponentStrategy) (chal : Claim),
      In member soc ->
      forall a, individual_defense member chal a -> cooperative_defense soc chal a.
    Proof.
      intros soc member chal Hin a Hdef.
      exact (power_of_assembly soc member Hin chal a Hdef).
    Qed.

    (* ---------------------------------------------------------------- *)
    (** *** The Shared Hologram (Cultural Memory) *)
    (* ---------------------------------------------------------------- *)

    (** In a society, impossibilities are SHARED.
        If Agent A discovers a wall, Agent B inherits that 'No' immediately.
        
        The shared hologram is the UNION of individual holograms.
        This is the "cultural memory" of accumulated refutations. *)
    Definition shared_hologram (member_holos : list Claim) : Claim :=
      fun a => exists h, In h member_holos /\ h a.

    (** The shared hologram contains every individual hologram *)
    Theorem individual_in_shared :
      forall member_holos h a,
      In h member_holos ->
      h a ->
      shared_hologram member_holos a.
    Proof.
      intros member_holos h a Hin Ha.
      exists h. split; assumption.
    Qed.

    (** THEOREM: Collective Existence (De Morgan for Society)
        
        The shared existence space is the INTERSECTION of individual 
        existence spaces. To be socially real, you must satisfy 
        everyone's constraints.
        
        shared_hologram = ∃h. h(a)         [Union of impossibilities]
        ~shared_hologram = ∀h. ~h(a)       [Intersection of possibilities] *)
    Theorem collective_existence :
      forall (member_holos : list Claim) a,
      ~ shared_hologram member_holos a <-> 
      forall h, In h member_holos -> ~ h a.
    Proof.
      intros member_holos a.
      unfold shared_hologram.
      split.
      - intros Hnot h Hin Ha. 
        apply Hnot. 
        exists h. auto.
      - intros Hall [h [Hin Ha]]. 
        exact (Hall h Hin Ha).
    Qed.

    (** Empty society has minimal hologram (just omega_veil) *)
    Theorem empty_society_hologram :
      forall a,
      ~ shared_hologram nil a.
    Proof.
      intros a [h [Hin _]].
      inversion Hin.
    Qed.

    (* ---------------------------------------------------------------- *)
    (** *** Social Coherence *)
    (* ---------------------------------------------------------------- *)

    (** A Society is coherent if there exists shared habitable ground:
        at least one position that is neither veiled nor in anyone's hologram. *)
    Definition socially_coherent (member_holos : list Claim) : Prop :=
      exists a, ~ omega_veil a /\ ~ shared_hologram member_holos a.

    (** A witness to coherence: any point outside all holograms *)
    Definition coherence_witness (member_holos : list Claim) (a : Position) : Prop :=
      ~ omega_veil a /\ ~ shared_hologram member_holos a.

    (** Any coherence witness proves coherence (constructive!) *)
    Theorem witness_implies_coherence :
      forall member_holos a,
      coherence_witness member_holos a ->
      socially_coherent member_holos.
    Proof.
      intros member_holos a [Hnot_veil Hnot_sh].
      exists a. split; assumption.
    Qed.

    (** Coherence unfolds to universal avoidance *)
    Theorem coherence_unfold :
      forall member_holos a,
      coherence_witness member_holos a <->
      ~ omega_veil a /\ (forall h, In h member_holos -> ~ h a).
    Proof.
      intros member_holos a.
      unfold coherence_witness.
      rewrite collective_existence.
      reflexivity.
    Qed.

    (* ---------------------------------------------------------------- *)
    (** *** Conflict and Compatibility *)
    (* ---------------------------------------------------------------- *)

    (** Two members conflict if their combined constraints leave no room.
        Constructively: we define this as the ABSENCE of a compatibility witness. *)
    Definition members_compatible (h1 h2 : Claim) : Prop :=
      exists a, ~ omega_veil a /\ ~ h1 a /\ ~ h2 a.

    Definition members_conflict (h1 h2 : Claim) : Prop :=
      ~ members_compatible h1 h2.

    (** A witness proves compatibility (constructive!) *)
    Theorem witness_proves_compatibility :
      forall h1 h2 a,
      ~ omega_veil a -> 
      ~ h1 a -> 
      ~ h2 a ->
      members_compatible h1 h2.
    Proof.
      intros h1 h2 a Hv H1 H2.
      exists a. repeat split; assumption.
    Qed.

    (** Compatibility is symmetric *)
    Theorem compatibility_symmetric :
      forall h1 h2,
      members_compatible h1 h2 -> members_compatible h2 h1.
    Proof.
      intros h1 h2 [a [Hv [H1 H2]]].
      exists a. repeat split; assumption.
    Qed.

    (** Conflict is symmetric *)
    Theorem conflict_symmetric :
      forall h1 h2,
      members_conflict h1 h2 -> members_conflict h2 h1.
    Proof.
      intros h1 h2 Hconf Hcompat.
      apply Hconf.
      apply compatibility_symmetric.
      exact Hcompat.
    Qed.

    (** Adding a conflicting member destroys coherence *)
    Theorem conflict_destroys_coherence :
      forall h_new existing_holos,
      socially_coherent existing_holos ->
      (forall a, coherence_witness existing_holos a -> h_new a) ->
      ~ socially_coherent (h_new :: existing_holos).
    Proof.
      intros h_new existing_holos [a [Hv Hsh]] Hconflict Hcoh.
      destruct Hcoh as [a' [Hv' Hsh']].
      unfold shared_hologram in Hsh'.
      apply Hsh'.
      exists h_new.
      split.
      - left. reflexivity.
      - apply Hconflict.
        unfold coherence_witness.
        split; [exact Hv' |].
        intro Hex.
        apply Hsh'.
        destruct Hex as [h [Hin Ha]].
        exists h. split; [right; exact Hin | exact Ha].
    Qed.

    (* ---------------------------------------------------------------- *)
    (** *** The Social Contract *)
    (* ---------------------------------------------------------------- *)

    (** The Social Contract: By joining a society, you inherit its hologram
        but gain access to its collective defense.
        
        Trade-off:
        - COST: Your existence space shrinks (more constraints)
        - GAIN: Your defense capacity grows (more strategies) *)

    Record SocialMembership := {
      member_strategy : ProponentStrategy;
      member_hologram : Claim;
      member_hologram_impossible : Is_Impossible member_hologram
    }.

    Definition member_list (members : list SocialMembership) : Society :=
      map member_strategy members.

    Definition hologram_list (members : list SocialMembership) : list Claim :=
      map member_hologram members.

    (** The fundamental trade-off of society *)
    Definition social_contract (members : list SocialMembership) : Prop :=
      (* Benefit: Cooperative defense *)
      (forall chal a, 
        cooperative_defense (member_list members) chal a ->
        exists m, In m members /\ individual_defense (member_strategy m) chal a)
      /\
      (* Cost: Shared hologram *)
      (forall a,
        shared_hologram (hologram_list members) a ->
        exists m, In m members /\ member_hologram m a).

    (** The social contract is always satisfied by construction *)
    Theorem social_contract_holds :
      forall members, social_contract members.
    Proof.
      intro members.
      split.
      - (* Benefit side *)
        intros chal a [strat [Hin Hdef]].
        unfold member_list in Hin.
        apply in_map_iff in Hin.
        destruct Hin as [m [Heq Hin]].
        exists m. split; [exact Hin |].
        subst strat. exact Hdef.
      - (* Cost side *)
        intros a [h [Hin Ha]].
        unfold hologram_list in Hin.
        apply in_map_iff in Hin.
        destruct Hin as [m [Heq Hin]].
        exists m. split; [exact Hin |].
        subst h. exact Ha.
    Qed.

  End GameDefinition.

End BoundaryGame.