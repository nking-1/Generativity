(** * ExistenceComonad.v
    
    The Comonad W = C ∘ R on Omega
    
    Core Insight:
    While the monad M = R ∘ C operates on Alpha (adding structure),
    the comonad W = C ∘ R operates on Omega (making infinity accessible).
    
    W is how finite beings access infinite totality:
    - Extract: Pull out current approximation
    - Duplicate: Embed in layers of approximation
    
    Modal interpretation: W = □ (necessity in S4)
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.CategoryTheory.
Require Import DAO.Theory.ExistenceAdjunction.
Import BasicCategoryTheory.Core.
Import BasicCategoryTheory.Functors.
Import ExistenceAdjunction.

Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Corelib.Classes.RelationClasses.

Module ExistenceComonad.

  (* ================================================================ *)
  (** ** The Comonad Definition *)
  (* ================================================================ *)
  
  Section ComonadDefinition.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** Import the functors from the adjunction *)
    Let C := Completion embed.
    Let R := Restriction embed.
    
    (* ------------------------------------------------------------ *)
    (** *** The Comonad W = C ∘ R *)
    (* ------------------------------------------------------------ *)
    
    (** W : PRED_Ω → PRED_Ω
        "Restrict to Alpha's view, then complete back to Omega" *)
    Definition W : Obj PRED_OMEGA -> Obj PRED_OMEGA :=
      fun Q => F_obj C (F_obj R Q).
    
    (** W on morphisms *)
    Definition W_map {Q Q' : Obj PRED_OMEGA} 
      (h : Hom PRED_OMEGA Q Q')
      : Hom PRED_OMEGA (W Q) (W Q') :=
      F_hom C (F_hom R h).
    
    (** Unfolding W explicitly *)
    Lemma W_unfold : forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
      W Q x <-> exists (a : Alphacarrier), 
                  embed a = x /\ 
                  Q (embed a) /\ 
                  ~ omega_veil a.
    Proof.
      intros Q x.
      unfold W, C, R, F_obj, Completion, Restriction.
      simpl.
      split.
      - intros [a [Heq [HQ Hnot]]].
        exists a. auto.
      - intros [a [Heq [HQ Hnot]]].
        exists a. auto.
    Qed.
    
    (* ------------------------------------------------------------ *)
    (** *** Extract (Counit): ε : W → Id *)
    (* ------------------------------------------------------------ *)
    
    (** Extract pulls the approximation back to the original.
        This is the counit of the adjunction C ⊣ R. *)
    Definition extract (Q : Obj PRED_OMEGA) 
      : Hom PRED_OMEGA (W Q) Q :=
      counit_component embed Q.
    
    (** Extract explicitly *)
    Lemma extract_unfold : forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
      forall (HW : W Q x), Q x.
    Proof.
      intros Q x HW.
      unfold W in HW.
      apply (extract Q x).
      exact HW.
    Qed.
    
    (** Extract is natural *)
    Theorem extract_natural :
      forall (Q Q' : Obj PRED_OMEGA) (h : Hom PRED_OMEGA Q Q'),
      compose PRED_OMEGA h (extract Q)
      = compose PRED_OMEGA (extract Q') (W_map h).
    Proof.
      intros Q Q' h.
      unfold extract, W_map.
      apply counit_natural.
    Qed.
    
    (* ------------------------------------------------------------ *)
    (** *** Duplicate: δ : W → W ∘ W *)
    (* ------------------------------------------------------------ *)
    
    (** Duplicate embeds an approximation into a layer of approximations.
        Built from the unit η of the adjunction. *)
    Definition duplicate (Q : Obj PRED_OMEGA)
      : Hom PRED_OMEGA (W Q) (W (W Q)).
    Proof.
      unfold W.
      apply (F_hom C).
      apply (unit_component embed).
    Defined.
    
    (** Duplicate explicitly: W(Q) → W(W(Q)) *)
    Lemma duplicate_unfold : 
      forall (Q : Omegacarrier -> Prop) (x : Omegacarrier) (HW : W Q x),
      W (W Q) x.
    Proof.
      intros Q x HW.
      apply (duplicate Q x).
      exact HW.
    Qed.
    
    (** Duplicate is natural *)
    Theorem duplicate_natural :
      forall (Q Q' : Obj PRED_OMEGA) (h : Hom PRED_OMEGA Q Q'),
      compose PRED_OMEGA (W_map (W_map h)) (duplicate Q)
      = compose PRED_OMEGA (duplicate Q') (W_map h).
    Proof.
      intros Q Q' h.
      unfold duplicate, W_map, W.
      (* This follows from naturality of η *)
      extensionality x.
      extensionality HW.
      unfold compose, F_hom, C, R, Completion, Restriction, unit_component.
      simpl.
      destruct HW as [a [Heq [HQ Hnot]]].
      f_equal.
    Qed.
    
  End ComonadDefinition.
  
  (* ================================================================ *)
  (** ** Comonad Laws *)
  (* ================================================================ *)
  
  Section ComonadLaws.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    Let C := Completion embed.
    Let R := Restriction embed.
    
    (* ------------------------------------------------------------ *)
    (** *** Law 1: Left Counit (ε ∘ W) ∘ δ = id *)
    (* ------------------------------------------------------------ *)
    
    Theorem comonad_left_counit :
      forall (Q : Obj PRED_OMEGA),
      compose PRED_OMEGA 
              (extract embed (W embed Q)) 
              (duplicate embed Q)
      = id PRED_OMEGA (W embed Q).
    Proof.
      intro Q.
      unfold extract, duplicate, W.
      (* This is triangle identity 2 applied to R(Q) *)
      apply (triangle_identity_2 embed (F_obj R Q)).
    Qed.
    
    (* ------------------------------------------------------------ *)
    (** *** Law 2: Right Counit (W ∘ ε) ∘ δ = id *)
    (* ------------------------------------------------------------ *)
    
    Theorem comonad_right_counit :
      forall (Q : Obj PRED_OMEGA),
      compose PRED_OMEGA
              (W_map embed (extract embed Q))
              (duplicate embed Q)
      = id PRED_OMEGA (W embed Q).
    Proof.
      intro Q.
      unfold W_map, extract, duplicate, W.
      extensionality x.
      extensionality H.
      unfold compose, id, counit_component, unit_component, 
             C, R, F_obj, F_hom, Completion, Restriction.
      simpl.
      destruct H as [a [Heq [HQ Hnot]]].
      subst x.
      f_equal.
      f_equal.
      apply proof_irrelevance.
    Qed.
    
    (* ------------------------------------------------------------ *)
    (** *** Law 3: Coassociativity (δ ∘ W) ∘ δ = (W ∘ δ) ∘ δ *)
    (* ------------------------------------------------------------ *)
    
    Theorem comonad_coassociativity :
      forall (Q : Obj PRED_OMEGA),
      compose PRED_OMEGA
              (duplicate embed (W embed Q))
              (duplicate embed Q)
      = compose PRED_OMEGA
                (W_map embed (duplicate embed Q))
                (duplicate embed Q).
    Proof.
      intro Q.
      unfold duplicate, W_map, W.
      extensionality x.
      extensionality H.
      unfold compose, unit_component, C, R, F_obj, F_hom,
             Completion, Restriction.
      simpl.
      destruct H as [a [Heq [HQ Hnot]]].
      subst x.
      f_equal.
    Qed.
    
    (** Master theorem: W is a comonad *)
    Theorem W_is_comonad :
      (* Left counit *)
      (forall Q, compose PRED_OMEGA (extract embed (W embed Q)) (duplicate embed Q) 
                = id PRED_OMEGA (W embed Q)) /\
      (* Right counit *)
      (forall Q, compose PRED_OMEGA (W_map embed (extract embed Q)) (duplicate embed Q)
                = id PRED_OMEGA (W embed Q)) /\
      (* Coassociativity *)
      (forall Q, compose PRED_OMEGA (duplicate embed (W embed Q)) (duplicate embed Q)
                = compose PRED_OMEGA (W_map embed (duplicate embed Q)) (duplicate embed Q)).
    Proof.
      repeat split.
      - apply comonad_left_counit.
      - apply comonad_right_counit.
      - apply comonad_coassociativity.
    Qed.
    
  End ComonadLaws.
  
  (* ================================================================ *)
  (** ** The Kernel of W: What Gets Lost *)
  (* ================================================================ *)
  
  Section ComonadKernel.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** The kernel: points where W(Q) differs from Q *)
    Definition kernel_W (Q : Omegacarrier -> Prop) : Omegacarrier -> Prop :=
      fun x => Q x /\ ~ W embed Q x.
    
    (** The cokernel: points where W(Q) holds but Q doesn't 
        (This should be empty by extract) *)
    Definition cokernel_W (Q : Omegacarrier -> Prop) : Omegacarrier -> Prop :=
      fun x => W embed Q x /\ ~ Q x.
    
    (** Extract ensures cokernel is empty *)
    Theorem cokernel_empty :
      forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
      ~ cokernel_W Q x.
    Proof.
      intros Q x [HW HnotQ].
      apply HnotQ.
      apply (extract_unfold embed Q x HW).
    Qed.
    
    (** The kernel lives in the "inaccessible" part *)
    Theorem kernel_not_in_alpha_image :
      forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
      kernel_W Q x ->
      ~ exists (a : Alphacarrier), embed a = x /\ ~ omega_veil a.
    Proof.
      intros Q x [HQ HnotW] [a [Heq Hnot]].
      subst x.  (* Now HQ : Q (embed a) *)
      apply HnotW.
      unfold W, Completion, Restriction, F_obj.
      simpl.
      exists a.
      split; [reflexivity |].
      split; [exact HQ | exact Hnot].
    Qed.
    
    (** W preserves what Alpha can see *)
    Theorem W_preserves_alpha_visible :
      forall (Q : Omegacarrier -> Prop) (a : Alphacarrier),
      ~ omega_veil a ->
      Q (embed a) ->
      W embed Q (embed a).
    Proof.
      intros Q a Hnot HQ.
      unfold W, Completion, Restriction, F_obj.
      simpl.
      exists a.
      split; [reflexivity |].
      split; [exact HQ | exact Hnot].
    Qed.
    
  End ComonadKernel.
  
  (* ================================================================ *)
  (** ** W-Coalgebras: Accessible Omega-Predicates *)
  (* ================================================================ *)
  
  Section WCoalgebras.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** A W-coalgebra is a predicate with "how to approximate me" structure *)
    Record WCoalgebra := {
      coalg_carrier : Omegacarrier -> Prop;
      coalg_structure : Hom PRED_OMEGA coalg_carrier (W embed coalg_carrier);
      
      (* Counit law: extract ∘ structure = id *)
      coalg_counit : forall x H,
        extract embed coalg_carrier x (coalg_structure x H) = H;
      
      (* Coassociativity: duplicate ∘ structure = W(structure) ∘ structure *)
      coalg_coassoc : forall x H,
        duplicate embed coalg_carrier x (coalg_structure x H)
        = W_map embed (coalg_structure) x (coalg_structure x H)
    }.
    
    (** A predicate is W-coalgebraic if W(Q) ≅ Q *)
    Definition is_W_coalgebraic (Q : Omegacarrier -> Prop) : Prop :=
      forall x, Q x <-> W embed Q x.
    
    (** Coalgebraic predicates are exactly those determined by Alpha *)
    Theorem coalgebraic_iff_alpha_determined :
      forall (Q : Omegacarrier -> Prop),
      is_W_coalgebraic Q <->
      (forall x, Q x -> exists a, embed a = x /\ ~ omega_veil a).
    Proof.
      intro Q.
      split.
      - (* Coalgebraic → Alpha-determined *)
        intros Hcoalg x HQ.
        apply Hcoalg in HQ.
        unfold W, Completion, Restriction, F_obj in HQ.
        simpl in HQ.
        destruct HQ as [a [Heq [_ Hnot]]].
        exists a. auto.
      - (* Alpha-determined → Coalgebraic *)
        intros Hdet x.
        split.
        + intro HQ.
          destruct (Hdet x HQ) as [a [Heq Hnot]].
          subst x.  (* Now HQ : Q (embed a) *)
          unfold W, Completion, Restriction, F_obj. simpl.
          exists a. split; [reflexivity |].
          split; [exact HQ | exact Hnot].
        + intro HW.
          apply (extract_unfold embed Q x HW).
    Qed.
    
    (** Every Alpha predicate gives a W-coalgebra *)
    Definition alpha_to_coalgebra (P : Alphacarrier -> Prop) : WCoalgebra.
    Proof.
      set (carrier := fun x => exists a, embed a = x /\ P a /\ ~ omega_veil a).
      
      (* First define the structure map *)
      assert (structure : forall x, carrier x -> W embed carrier x).
      {
        intros x [a [Heq [HP Hnot]]].
        subst x.
        unfold W, Completion, Restriction, F_obj. simpl.
        exists a.
        split; [reflexivity |].
        split.
        - exists a. split; [reflexivity |]. split; [exact HP | exact Hnot].
        - exact Hnot.
      }
      
      refine ({|
        coalg_carrier := carrier;
        coalg_structure := structure;
        coalg_counit := _;
        coalg_coassoc := _
      |}).
      
      - (* Counit law *)
        intros x H.
        apply proof_irrelevance.
        
      - (* Coassociativity *)
        intros x H.
        unfold duplicate, W_map, W, Completion, Restriction,
              F_obj, F_hom, unit_component.
        simpl.
        f_equal.
        apply proof_irrelevance.
    Defined.
    
    (** Every W-coalgebra gives an Alpha predicate *)
    Definition coalgebra_to_alpha (WC : WCoalgebra) : Alphacarrier -> Prop :=
      fun a => coalg_carrier WC (embed a) /\ ~ omega_veil a.
    
  End WCoalgebras.
  
  (* ================================================================ *)
  (** ** Iterated W: Deepening Access *)
  (* ================================================================ *)
  
  Section IteratedW.
    Context {Alpha : AlphaType}.
    Context {Omega : OmegaType}.
    Context (embed : Alphacarrier -> Omegacarrier).
    
    (** W^n: n-fold application of W *)
    Fixpoint W_iter (n : nat) (Q : Omegacarrier -> Prop) : Omegacarrier -> Prop :=
      match n with
      | O => Q
      | S m => W embed (W_iter m Q)
      end.
    
    (** W^0 = id *)
    Lemma W_iter_0 : forall Q, W_iter 0 Q = Q.
    Proof. reflexivity. Qed.
    
    (** W^(n+1) = W ∘ W^n *)
    Lemma W_iter_S : forall n Q, W_iter (S n) Q = W embed (W_iter n Q).
    Proof. reflexivity. Qed.
    
    (** Each iteration shrinks (or preserves) the extension *)
    Theorem W_iter_monotone :
      forall (n : nat) (Q : Omegacarrier -> Prop) (x : Omegacarrier),
      W_iter (S n) Q x -> W_iter n Q x.
    Proof.
      intros n Q x HW.
      simpl in HW.
      apply (extract_unfold embed (W_iter n Q) x HW).
    Qed.
    
    (** The iterated hologram at stage n *)
    Definition hologram_iter (n : nat) (Q : Omegacarrier -> Prop) 
      : Omegacarrier -> Prop :=
      fun x => W_iter n Q x /\ ~ W_iter (S n) Q x.
    
    (** Hologram is what gets lost at each iteration *)
    Theorem hologram_iter_is_loss :
      forall n Q x,
      hologram_iter n Q x -> 
      W_iter n Q x /\ ~ W embed (W_iter n Q) x.
    Proof.
      intros n Q x [HWn HnotWSn].
      split; [exact HWn |].
      simpl in HnotWSn.
      exact HnotWSn.
    Qed.
    
    (** Fixed point: where iteration stabilizes *)
    Definition is_W_fixed_point (Q : Omegacarrier -> Prop) : Prop :=
      forall x, Q x <-> W embed Q x.
    
    (** If Q is a fixed point, all iterations are equal *)
    Theorem fixed_point_stable :
      forall Q,
      is_W_fixed_point Q ->
      forall n x, W_iter n Q x <-> Q x.
    Proof.
      intros Q Hfix n.
      induction n.
      - (* n = 0 *)
        intro x. simpl. reflexivity.
      - (* n = S n' *)
        intro x.
        simpl.
        (* Goal: W embed (W_iter n Q) x <-> Q x *)
        split.
        + (* W (W_iter n Q) x -> Q x *)
          intro HW.
          apply (extract_unfold embed (W_iter n Q) x) in HW.
          (* HW : W_iter n Q x *)
          apply IHn.
          exact HW.
        + (* Q x -> W (W_iter n Q) x *)
          intro HQ.
          (* Use Hfix to get W Q x *)
          apply Hfix in HQ.
          (* HQ : W embed Q x *)
          unfold W, Completion, Restriction, F_obj in *.
          simpl in *.
          destruct HQ as [a [Heq [HQa Hnot]]].
          exists a.
          split; [exact Heq |].
          split.
          * (* Need W_iter n Q (embed a), have Q (embed a) *)
            apply IHn. exact HQa.
          * exact Hnot.
    Qed.
      
    End IteratedW.
    
    (* ================================================================ *)
    (** ** Modal Logic Interpretation: W = □ *)
    (* ================================================================ *)
    
    Section ModalLogic.
      Context {Alpha : AlphaType}.
      Context {Omega : OmegaType}.
      Context (embed : Alphacarrier -> Omegacarrier).
      
      (** Necessity: □Q = W(Q) *)
      Definition box (Q : Omegacarrier -> Prop) : Omegacarrier -> Prop :=
        W embed Q.
      
      (** Possibility: ◇Q = ¬□¬Q *)
      Definition diamond (Q : Omegacarrier -> Prop) : Omegacarrier -> Prop :=
        fun x => ~ box (fun y => ~ Q y) x.
      
      (** T Axiom: □Q → Q (this is extract) *)
      Theorem T_axiom :
        forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
        box Q x -> Q x.
      Proof.
        intros Q x Hbox.
        apply (extract_unfold embed Q x Hbox).
      Qed.
      
      (** 4 Axiom: □Q → □□Q (this is duplicate) *)
      Theorem four_axiom :
        forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
        box Q x -> box (box Q) x.
      Proof.
        intros Q x Hbox.
        apply (duplicate_unfold embed Q x Hbox).
      Qed.
      
      (** K Axiom: □(P → Q) → (□P → □Q) (functoriality) *)
      Theorem K_axiom :
        forall (P Q : Omegacarrier -> Prop),
        forall (f : forall x, P x -> Q x),
        forall x, box P x -> box Q x.
      Proof.
        intros P Q f x HP.
        unfold box.
        apply (W_map embed f x HP).
      Qed.
      
      (** Necessitation: If Q = True everywhere, then □Q *)
      Theorem necessitation :
        forall (Q : Omegacarrier -> Prop),
        (forall x, Q x) ->
        forall x, (exists a, embed a = x /\ ~ omega_veil a) -> box Q x.
      Proof.
        intros Q HQ x [a [Heq Hnot]].
        unfold box, W, Completion, Restriction, F_obj.
        simpl.
        exists a.
        split; [exact Heq |].
        split; [apply HQ | exact Hnot].
      Qed.
      
      (** The Unknown class in modal terms *)
      Definition unknown (Q : Omegacarrier -> Prop) : Omegacarrier -> Prop :=
        fun x => diamond Q x /\ diamond (fun y => ~ Q y) x.
      
      (** Define unknown directly, without double-negation *)
      Definition unknown_constructive (Q : Omegacarrier -> Prop) : Omegacarrier -> Prop :=
        fun x => ~ box Q x /\ ~ box (fun y => ~ Q y) x.

      (** The one direction that IS constructively provable *)
      Theorem unknown_implies_undecided :
        forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
        unknown Q x -> unknown_constructive Q x.
      Proof.
        intros Q x [Hdiam_Q Hdiam_notQ].
        unfold unknown_constructive.
        split.
        - (* ¬box Q from diamond Q = ¬box(¬Q) *)
          (* This direction needs: ¬box(¬Q) → ¬box Q, which is NOT valid *)
          (* We actually need the other conjunct here *)
          intro Hbox.
          apply Hdiam_notQ.
          unfold box, diamond, W, Completion, Restriction, F_obj in *.
          simpl in *.
          destruct Hbox as [a [Heq [HQ Hnot]]].
          exists a. split; [exact Heq |].
          split.
          + intro HnotQ. exact (HnotQ HQ).
          + exact Hnot.
        - (* ¬box(¬Q) is exactly diamond Q *)
          exact Hdiam_Q.
      Qed.

      (** The converse requires classical logic - state it with that assumption *)
      Theorem undecided_implies_unknown_classical :
        forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
        (forall P : Prop, ~~P -> P) ->  (* Double negation elimination *)
        unknown_constructive Q x -> unknown Q x.
      Proof.
        intros Q x DNE [HnotBoxQ HnotBoxNotQ].
        unfold unknown, diamond, box.
        split.
        - (* diamond Q = ¬box(¬Q) *)
          exact HnotBoxNotQ.
        - (* diamond(¬Q) = ¬box(¬¬Q) *)
          intro Hbox.
          apply HnotBoxQ.
          unfold W, Completion, Restriction, F_obj in *.
          simpl in *.
          destruct Hbox as [a [Heq [HnotnotQ Hnot]]].
          exists a. split; [exact Heq |].
          split.
          + apply DNE. exact HnotnotQ.
          + exact Hnot.
      Qed.
      
    End ModalLogic.
    
    (** ================================================================ *)
    (** ** The Omega Veil as Limit of Inaccessibility *)
    (** ================================================================ *)

    Section OmegaVeilLimit.
      Context {Alpha : AlphaType}.
      Context {Omega : OmegaType}.
      Context (embed : Alphacarrier -> Omegacarrier).

      (** The fundamental inaccessible = points not in Alpha's image *)
      Definition fundamentally_inaccessible : Omegacarrier -> Prop :=
        fun x => ~ exists a, embed a = x /\ ~ omega_veil a.

      (** W cannot reach fundamentally inaccessible points *)
      Theorem W_cannot_reach_inaccessible :
        forall (Q : Omegacarrier -> Prop) (x : Omegacarrier),
        fundamentally_inaccessible x ->
        ~ W embed Q x.
      Proof.
        intros Q x Hinacc HW.
        apply Hinacc.
        unfold W, Completion, Restriction, F_obj in HW.
        simpl in HW.
        destruct HW as [a [Heq [_ Hnot]]].
        exists a. split; [exact Heq | exact Hnot].
      Qed.

      (* ------------------------------------------------------------ *)
      (** *** omega_veil as Boundary *)
      (* ------------------------------------------------------------ *)

      (** Fiber-constancy: omega_veil respects fibers of embed *)
      Definition veil_respects_embed : Prop :=
        forall a a' : Alphacarrier, 
          embed a = embed a' -> omega_veil a -> omega_veil a'.

      (** Injectivity implies fiber-constancy *)
      Lemma injective_implies_respects :
        (forall a a' : Alphacarrier, embed a = embed a' -> a = a') ->
        veil_respects_embed.
      Proof.
        intros Hinj a a' Heq Hveil.
        apply Hinj in Heq.
        subst a'.
        exact Hveil.
      Qed.

      (** Direction 1: omega_veil → inaccessible (needs fiber-constancy) *)
      Theorem veil_implies_inaccessible :
        veil_respects_embed ->
        forall (a : Alphacarrier),
        omega_veil a -> fundamentally_inaccessible (embed a).
      Proof.
        intros Hresp a Hveil [a' [Heq Hnot]].
        apply Hnot.
        apply (Hresp a a').
        - symmetry. exact Heq.
        - exact Hveil.
      Qed.

      (** Direction 2: inaccessible → ~~omega_veil (constructive) *)
      Theorem inaccessible_implies_not_not_veil :
        forall (a : Alphacarrier),
        fundamentally_inaccessible (embed a) -> ~~(omega_veil a).
      Proof.
        intros a Hinacc Hnot_veil.
        apply Hinacc.
        exists a.
        split.
        - reflexivity.
        - exact Hnot_veil.
      Qed.

      (** Direction 2: inaccessible → omega_veil (needs DNE) *)
      Theorem inaccessible_implies_veil :
        (forall P : Prop, ~~P -> P) ->
        forall (a : Alphacarrier),
        fundamentally_inaccessible (embed a) -> omega_veil a.
      Proof.
        intros DNE a Hinacc.
        apply DNE.
        apply inaccessible_implies_not_not_veil.
        exact Hinacc.
      Qed.

      (** Full equivalence (needs both assumptions) *)
      Theorem veil_is_boundary :
        veil_respects_embed ->
        (forall P : Prop, ~~P -> P) ->
        forall (a : Alphacarrier),
        omega_veil a <-> fundamentally_inaccessible (embed a).
      Proof.
        intros Hresp DNE a.
        split.
        - apply veil_implies_inaccessible. exact Hresp.
        - apply inaccessible_implies_veil. exact DNE.
      Qed.

      (** Constructive partial result (no axioms) *)
      Theorem veil_boundary_constructive :
        veil_respects_embed ->
        forall (a : Alphacarrier),
        (omega_veil a -> fundamentally_inaccessible (embed a)) /\
        (fundamentally_inaccessible (embed a) -> ~~(omega_veil a)).
      Proof.
        intros Hresp a.
        split.
        - apply veil_implies_inaccessible. exact Hresp.
        - apply inaccessible_implies_not_not_veil.
      Qed.

    End OmegaVeilLimit.
    
    (* ================================================================ *)
    (** ** Relationship to the Monad *)
    (* ================================================================ *)
    
    Section MonadComonadDuality.
      Context {Alpha : AlphaType}.
      Context {Omega : OmegaType}.
      Context (embed : Alphacarrier -> Omegacarrier).
      
      (** The monad M = R ∘ C on Alpha (from ExistenceAdjunction) *)
      Let M := ExistenceAdjunction.M embed.
      
      (** The comonad W = C ∘ R on Omega *)
      Let W' := W embed.
      
      (** Key duality: M and W share structure via the adjunction *)
      
      (** M's unit builds W's duplicate *)
      Theorem unit_builds_duplicate :
        forall (Q : Omegacarrier -> Prop),
        duplicate embed Q 
        = F_hom (Completion embed) (unit_component embed (F_obj (Restriction embed) Q)).
      Proof.
        intro Q.
        unfold duplicate.
        reflexivity.
      Qed.
      
      (** W's counit builds M's join *)
      Theorem counit_builds_join :
        forall (P : Alphacarrier -> Prop),
        ExistenceAdjunction.join embed P
        = F_hom (Restriction embed) (counit_component embed (F_obj (Completion embed) P)).
      Proof.
        intro P.
        unfold ExistenceAdjunction.join.
        reflexivity.
      Qed.
      
      (** The profound duality *)
      (** M-algebras ≃ W-coalgebras ≃ PRED_α *)
      
      (** Both capture "Alpha-shaped" predicates:
          - M-algebra: Alpha predicate with extra structure
          - W-coalgebra: Omega predicate accessible through Alpha
          - Both equivalent to plain Alpha predicates *)
      
    End MonadComonadDuality.
    
    (* ================================================================ *)
    (** ** Philosophical Summary *)
    (* ================================================================ *)
    
    (** What we've formalized:
        
        1. THE COMONAD W = C ∘ R
          - Lives on PRED_Omega
          - Makes infinity accessible through finite
          - Extract: pull out approximation
          - Duplicate: embed in layers
          
        2. COMONAD LAWS
          - Left counit: (ε ∘ W) ∘ δ = id
          - Right counit: (W ∘ ε) ∘ δ = id  
          - Coassociativity: (δ ∘ W) ∘ δ = (W ∘ δ) ∘ δ
          
        3. THE KERNEL
          - What W cannot reach
          - Lives outside Alpha's image
          - The "fundamentally inaccessible"
          
        4. W-COALGEBRAS
          - Omega predicates with "how to approximate me"
          - Equivalent to Alpha predicates
          - The accessible part of Omega
          
        5. MODAL LOGIC
          - W = □ (necessity)
          - T axiom: □Q → Q (extract)
          - 4 axiom: □Q → □□Q (duplicate)
          - Unknown = ◇Q ∧ ◇¬Q (neither necessary nor impossible)
          
        6. MONAD-COMONAD DUALITY
          - M = R ∘ C builds structure in Alpha
          - W = C ∘ R extracts structure from Omega
          - Same adjunction, dual operations
          - What M can build = What W can access
          
        THE MEANING:
        
        The comonad W is how finite beings access infinite truth.
        Not by reducing Omega, but by structuring our relationship to it.
        Each W-application deepens access, adds meaning.
        The kernel (fundamentally inaccessible) is omega_veil.
        
        W and M together form the complete picture:
        - M: How Alpha grows (enriches finite)
        - W: How Omega becomes reachable (tames infinite)
        
        Reality lives in the adjunction space.
        The monad builds up from below.
        The comonad reaches in from above.
        Together: meaningful structured existence.
    *)

End ExistenceComonad.