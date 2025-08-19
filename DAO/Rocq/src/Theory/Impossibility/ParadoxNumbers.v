(** * ParadoxNaturals.v
    
    Numbers as construction depths of paradoxes.
    All paradoxes equal omega_veil, but their construction history gives us arithmetic.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import DAO.Theory.Impossibility.WaysOfNotExisting.
Require Import ZArith.

Module ParadoxNumbers.
  Module ParadoxNaturals.
    Import ImpossibilityAlgebra Core.
    Import WaysOfNotExisting PatternEquivalence.
  
    Section VonNeumannParadox.
      Context {Alpha : AlphaType}.

      (* ================================================================ *)
      (** ** Numbers as Types: Von Neumann Ordinals via Paradox *)
      (* ================================================================ *)

      (* Zero is the type of things satisfying omega_veil - necessarily empty *)
      Definition ZeroT : Type := { a : Alphacarrier | omega_veil a }.

      (* Zero has no inhabitants *)
      Theorem zero_empty : ZeroT -> False.
      Proof.
        intros [a Ha].
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Ha).
      Qed.

      (* Successor creates a paradox type *)
      Inductive SuccT (T : Type) : Type :=
        | mk_paradox : T -> (T -> False) -> SuccT T.

      (* Numbers are types *)
      Definition OneT := SuccT ZeroT.
      Definition TwoT := SuccT OneT.
      Definition ThreeT := SuccT TwoT.

      (* All number types are empty (uninhabited) *)
      Theorem one_empty : OneT -> False.
      Proof.
        intro one.
        destruct one as [z not_z].
        (* z : ZeroT and not_z : ZeroT -> False *)
        exact (not_z z).
      Qed.

      Theorem two_empty : TwoT -> False.
      Proof.
        intro two.
        destruct two as [one not_one].
        exact (not_one one).
      Qed.

      (* General theorem: all successor types are empty *)
      Theorem succ_empty : forall T : Type, SuccT T -> False.
      Proof.
        intros T s.
        destruct s as [t not_t].
        exact (not_t t).
      Qed.

      (* ================================================================ *)
      (** ** Building Natural Numbers as a Type Family *)
      (* ================================================================ *)

      (* Natural numbers as an inductive type indexing our paradox types *)
      Inductive PNatT : Type :=
        | ZT : PNatT
        | ST : PNatT -> PNatT.

      (* Map each PNatT to its corresponding paradox type *)
      Fixpoint to_paradox_type (n : PNatT) : Type :=
        match n with
        | ZT => ZeroT
        | ST m => SuccT (to_paradox_type m)
        end.

      (* All paradox types are empty *)
      Theorem all_paradox_types_empty : forall n : PNatT,
        to_paradox_type n -> False.
      Proof.
        intro n.
        induction n.
        - (* ZT case *)
          apply zero_empty.
        - (* ST case *)
          intro s.
          destruct s as [t not_t].
          exact (not_t t).
      Qed.

      (* ================================================================ *)
      (** ** Arithmetic on Paradox Types *)
      (* ================================================================ *)

      (* Addition: combine the paradox structures *)
      Fixpoint addT (m n : PNatT) : PNatT :=
        match m with
        | ZT => n
        | ST m' => ST (addT m' n)
        end.

      (* Multiplication: iterate the paradox *)
      Fixpoint multT (m n : PNatT) : PNatT :=
        match m with
        | ZT => ZT
        | ST m' => addT n (multT m' n)
        end.

      (* Addition preserves the paradox structure *)
      Theorem add_preserves_emptiness : forall m n : PNatT,
        to_paradox_type (addT m n) -> False.
      Proof.
        intros m n.
        apply all_paradox_types_empty.
      Qed.

      (* ================================================================ *)
      (** ** The Equivalence to Von Neumann Ordinals *)
      (* ================================================================ *)

      (* Von Neumann: 0 = ∅, 1 = {∅}, 2 = {∅, {∅}}, ... *)
      (* Ours: 0 = omega_veil, 1 = paradox(0), 2 = paradox(1), ... *)

      (* The key insight: both are building structure from emptiness *)
      (* Von Neumann uses set membership, we use paradox construction *)

      (* A "set" in our framework is a type *)
      Definition SetT := Type.

      (* The empty set is ZeroT *)
      Definition empty_set : SetT := ZeroT.

      (* The singleton {∅} is OneT - it "contains" zero via paradox *)
      Definition singleton_empty : SetT := OneT.

      (* In von Neumann ordinals, each number contains all smaller numbers *)
      (* So we need a recursive membership relation *)
      Fixpoint contains_vn (inner outer : PNatT) : Prop :=
      match outer with
      | ZT => False  (* Zero contains nothing *)
      | ST m => (inner = m) \/ contains_vn inner m  
        (* Successor contains its predecessor AND everything the predecessor contains *)
      end.

      (* This gives us the true von Neumann structure *)
      Theorem von_neumann_structure : 
      (* 0 = ∅ *)
      (forall x, ~contains_vn x ZT) /\
      (* 1 = {0} *)
      (contains_vn ZT (ST ZT)) /\
      (* 2 = {0, 1} *)
      (contains_vn ZT (ST (ST ZT)) /\ contains_vn (ST ZT) (ST (ST ZT))).
      Proof.
      split; [|split; [|split]].
      - (* 0 contains nothing *)
        intros x. simpl. auto.
      - (* 1 contains 0 *)
        simpl. left. reflexivity.
      - (* 2 contains 0 *)
        simpl. right. left. reflexivity.
      - (* 2 contains 1 *)
        simpl. left. reflexivity.
      Qed.

      (* The crucial theorem: n+1 contains exactly 0 through n *)
      Theorem von_neumann_characterization : forall n m : PNatT,
      contains_vn m (ST n) <-> (m = n \/ contains_vn m n).
      Proof.
      intros n m.
      simpl.
      split; intro H; exact H.
      Qed.

      (* This perfectly mirrors von Neumann's n = {0, 1, ..., n-1} *)
      
      (* ================================================================ *)
      (** ** The Peano Structure *)
      (* ================================================================ *)
      
      (* Zero is not a successor *)
      Theorem zero_not_succ : forall n : PNatT, ZT <> ST n.
      Proof.
        intros n H.
        discriminate H.
      Qed.
      
      (* Successor is injective *)
      Theorem succ_injective_vn : forall m n : PNatT, 
        ST m = ST n -> m = n.
      Proof.
        intros m n H.
        injection H. auto.
      Qed.
      
      (* Induction principle *)
      Theorem nat_induction : forall (P : PNatT -> Prop),
        P ZT ->
        (forall n, P n -> P (ST n)) ->
        forall n, P n.
      Proof.
        intros P HZ HS n.
        induction n.
        - exact HZ.
        - apply HS. exact IHn.
      Qed.
      
      (* ================================================================ *)
      (** ** The Philosophical Victory *)
      (* ================================================================ *)
      
      (* We've built natural numbers where: *)
      (* 1. Each number is a TYPE (not a value) *)
      (* 2. All types are EMPTY (paradoxical) *)
      (* 3. The structure IS the number *)
      (* 4. Arithmetic works on the structure *)
      
      (* The correspondence to von Neumann: *)
      (* Von Neumann: n+1 = n ∪ {n} *)
      (* Ours: (n+1)T = SuccT(nT) = type of paradoxes about nT *)
      
      (* Both build numbers from structured emptiness, *)
      (* but ours uses type theory instead of set theory! *)
      
      (* Example: Two is literally the type of paradoxes about paradoxes about void *)
      Example two_is_double_paradox : 
        TwoT = SuccT (SuccT ZeroT).
      Proof.
        reflexivity.
      Qed.
      
      (* And this type structure gives us computation *)
      Example one_plus_one : 
        addT (ST ZT) (ST ZT) = ST (ST ZT).
      Proof.
        reflexivity.
      Qed.
      
      (* The numbers work, even though they're all impossible! *)
      
  End VonNeumannParadox.

    Section PureParadoxConstruction.
 Context {Alpha : AlphaType}.
 
 (* ================================================================ *)
 (** ** The Foundation: Building Numbers from Pure Paradox *)
 (* ================================================================ *)
 
 (* The first paradox - the unit of construction *)
 Definition first_paradox : Alphacarrier -> Prop :=
   fun a => omega_veil a /\ ~omega_veil a.
 
 (* The successor operation - add another layer of paradox *)
 Definition next_paradox (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
   fun a => P a /\ ~P a.
 
 (* Build paradox patterns of any depth *)
 Fixpoint paradox_depth (n : nat) : Alphacarrier -> Prop :=
   match n with
   | 0 => omega_veil                           (* Zero is the void itself *)
   | S m => next_paradox (paradox_depth m)     (* Each successor adds a layer *)
   end.
 
 (* Prove all depths are impossible *)
 Lemma paradox_depth_impossible : forall n : nat,
   ImpossibilityAlgebra.Core.Is_Impossible (paradox_depth n).
 Proof.
   intro n.
   induction n.
   - (* Base case: omega_veil *)
     intro a. simpl. split; intro H; exact H.
   - (* Inductive case: next_paradox *)
     intro a. simpl.
     unfold next_paradox.
     split.
     + (* Forward *)
       intros [H_prev H_not_prev].
       (* This is contradictory *)
       exfalso. exact (H_not_prev H_prev).
     + (* Backward *)
       intro H_omega.
       exfalso.
       exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H_omega).
 Qed.
 
 (* ================================================================ *)
 (** ** Numbers as Equivalence Classes of Paradox Patterns *)
 (* ================================================================ *)
 
 (* A natural number IS an equivalence class of patterns at depth n *)
 Definition ParadoxNat (n : nat) := 
   { P : Alphacarrier -> Prop | 
     PatternEquivalence.pattern_equiv P (paradox_depth n) }.
 
 (* Constructor for the canonical representative *)
 Definition make_nat (n : nat) : ParadoxNat n.
 Proof.
   exists (paradox_depth n).
   unfold PatternEquivalence.pattern_equiv.
   split; [|split].
   - apply paradox_depth_impossible.
   - apply paradox_depth_impossible.
   - intro w. split; intro H; exact H.
 Defined.
 
 (* The first few numbers *)
 Definition Zero : ParadoxNat 0 := make_nat 0.
 Definition One : ParadoxNat 1 := make_nat 1.
 Definition Two : ParadoxNat 2 := make_nat 2.
 Definition Three : ParadoxNat 3 := make_nat 3.
 
 (* ================================================================ *)
 (** ** Arithmetic Operations on Paradox Patterns *)
 (* ================================================================ *)
 
 (* Addition combines paradox depths *)
 Definition add_paradox_patterns (m n : nat) : Alphacarrier -> Prop :=
   paradox_depth (m + n).
 
 (* Addition for our paradox naturals *)
 Definition paradox_add {m n : nat} 
   (x : ParadoxNat m) (y : ParadoxNat n) : ParadoxNat (m + n).
 Proof.
   exists (add_paradox_patterns m n).
   unfold add_paradox_patterns.
   unfold PatternEquivalence.pattern_equiv.
   split; [|split].
   - apply paradox_depth_impossible.
   - apply paradox_depth_impossible.
   - intro w. split; intro H; exact H.
 Defined.
 
 (* Multiplication iterates paradox construction *)
 Definition mult_paradox_patterns (m n : nat) : Alphacarrier -> Prop :=
   paradox_depth (m * n).
 
 Definition paradox_mult {m n : nat}
   (x : ParadoxNat m) (y : ParadoxNat n) : ParadoxNat (m * n).
 Proof.
   exists (mult_paradox_patterns m n).
   unfold mult_paradox_patterns.
   unfold PatternEquivalence.pattern_equiv.
   split; [|split].
   - apply paradox_depth_impossible.
   - apply paradox_depth_impossible.
   - intro w. split; intro H; exact H.
 Defined.
 
 (* ================================================================ *)
 (** ** The Successor Operation *)
 (* ================================================================ *)
 
 (* Successor adds one more paradox layer *)
 Definition paradox_successor {n : nat} (x : ParadoxNat n) : ParadoxNat (S n).
 Proof.
   (* Extract the pattern from x *)
   destruct x as [P [H_imp_P [H_imp_depth H_equiv]]].
   (* Build the next paradox *)
   exists (next_paradox P).
   unfold PatternEquivalence.pattern_equiv.
   split; [|split].
   - (* next_paradox P is impossible *)
     intro a. unfold next_paradox.
     split.
     + intros [HP HnP]. exfalso. exact (HnP HP).
     + intro H. exfalso.
       exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
   - (* paradox_depth (S n) is impossible *)
     apply paradox_depth_impossible.
   - (* They're extensionally equal *)
     intro w.
     simpl.
     unfold next_paradox.
     (* Both sides are impossible, so they're equal to omega_veil *)
     split; intro H.
     + (* next_paradox P w -> paradox_depth n w /\ ~paradox_depth n w *)
       destruct H as [HPw HnPw].
       split.
       * (* P w -> paradox_depth n w *)
         apply H_equiv. exact HPw.
       * (* ~paradox_depth n w *)
         intro H_depth.
         apply HnPw.
         apply H_equiv.
         exact H_depth.
     + (* paradox_depth n w /\ ~paradox_depth n w -> next_paradox P w *)
       destruct H as [H_depth Hn_depth].
       split.
       * (* P w *)
         apply H_equiv. exact H_depth.
       * (* ~P w *)
         intro HPw.
         apply Hn_depth.
         apply H_equiv.
         exact HPw.
 Defined.
 
 (* ================================================================ *)
 (** ** Properties and Theorems *)
 (* ================================================================ *)
 
 (* All paradox naturals are built from impossible patterns *)
 Theorem all_paradox_nats_impossible : forall n (x : ParadoxNat n),
   ImpossibilityAlgebra.Core.Is_Impossible (proj1_sig x).
 Proof.
   intros n x.
   destruct x as [P [H_imp_P dc]].
   exact H_imp_P.
 Qed.
 
 Axiom ParadoxNat_injective : forall m n : nat,
  ParadoxNat m = ParadoxNat n -> m = n.

Theorem successor_injective : forall m n,
  ParadoxNat (S m) = ParadoxNat (S n) -> m = n.
Proof.
  intros m n H.
  apply ParadoxNat_injective in H.
  injection H. auto.
Qed.

Theorem zero_not_successor : forall n,
  ParadoxNat 0 <> ParadoxNat (S n).
Proof.
  intros n H.
  apply ParadoxNat_injective in H.
  discriminate H.
Qed.
 
 (* ================================================================ *)
 (** ** The Philosophy: What We've Built *)
 (* ================================================================ *)
 
 (* Numbers ARE paradox patterns - not built from them, but BEING them *)
 Theorem numbers_are_paradoxes : forall n,
   exists P : Alphacarrier -> Prop,
   ImpossibilityAlgebra.Core.Is_Impossible P /\
   ParadoxNat n = { Q | PatternEquivalence.pattern_equiv Q P }.
 Proof.
   intro n.
   exists (paradox_depth n).
   split.
   - apply paradox_depth_impossible.
   - reflexivity.
 Qed.
 
 (* Each number has a canonical paradox representation *)
 Definition canonical_paradox (n : nat) : Alphacarrier -> Prop :=
   paradox_depth n.
 
 (* The construction principle: numbers emerge from iterating paradox *)
 Theorem construction_principle : forall n,
   canonical_paradox (S n) = next_paradox (canonical_paradox n).
 Proof.
   intro n.
   reflexivity.
 Qed.
 
 (* Zero is the void, One is the first construction, etc. *)
 Theorem number_meanings :
   (canonical_paradox 0 = omega_veil) /\
   (canonical_paradox 1 = first_paradox) /\
   (canonical_paradox 2 = next_paradox first_paradox).
 Proof.
   split; [|split]; reflexivity.
 Qed.
 
 (* ================================================================ *)
 (** ** Examples *)
 (* ================================================================ *)
 
Example two_plus_three_pattern : 
  add_paradox_patterns 2 3 = paradox_depth 5.
Proof.
  unfold add_paradox_patterns.
  simpl. reflexivity.
Qed.

Example two_times_three_pattern :
  mult_paradox_patterns 2 3 = paradox_depth 6.
Proof.
  unfold mult_paradox_patterns.
  simpl. reflexivity.
Qed.
 
End PureParadoxConstruction.

    Section PureParadoxNaturals.
      Context {Alpha : AlphaType}.
      
      (** ** Natural numbers start at 1 - they are CONSTRUCTIONS beyond void *)
      
      (* Natural numbers are positive constructions *)
      Inductive PNat : Type :=
        | POne : PNat              (* First construction = 1 *)
        | PS : PNat -> PNat.       (* Successor *)
      
      (* Each natural is a construction depth beyond the void *)
      Fixpoint paradox_at (n : PNat) : Alphacarrier -> Prop :=
        match n with
        | POne => fun a => omega_veil a /\ ~ omega_veil a  (* First paradox construction *)
        | PS m => fun a => paradox_at m a /\ ~ paradox_at m a  (* Layer more paradox *)
        end.
      
      (* All levels are impossible *)
      Theorem all_impossible : forall n : PNat, Is_Impossible (paradox_at n).
      Proof.
        intro n.
        induction n.
        - (* POne case *)
          intro a. simpl.
          split.
          + intros [H _]. exact H.
          + intro Hov. exfalso.
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hov).
        - (* PS case *)
          intro a. simpl.
          split.
          + intros [H _]. apply IHn. exact H.
          + intro Hov. exfalso.
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hov).
      Qed.
      
      (** ** Arithmetic *)
      
      Fixpoint add (m n : PNat) : PNat :=
        match m with
        | POne => PS n           (* 1 + n = n + 1 *)
        | PS m' => PS (add m' n)
        end.
      
      Fixpoint mult (m n : PNat) : PNat :=
        match m with
        | POne => n              (* 1 * n = n *)
        | PS m' => add n (mult m' n)
        end.
      
      (** ** Modified Peano Axioms (starting from 1) *)
      
      Theorem one_not_succ : forall n : PNat, POne <> PS n.
      Proof.
        intros n H.
        discriminate H.
      Qed.
      
      Theorem succ_injective : forall m n : PNat, PS m = PS n -> m = n.
      Proof.
        intros m n H.
        injection H. auto.
      Qed.
      
      (** ** Connection to Coq's nat (which includes 0) *)
      
      Fixpoint pnat_to_coq_nat (n : PNat) : nat :=
        match n with
        | POne => 1
        | PS m => S (pnat_to_coq_nat m)
        end.
      
      Fixpoint coq_nat_to_pnat (n : nat) : option PNat :=
        match n with
        | 0 => None              (* 0 has no PNat representation! *)
        | S m => 
            match coq_nat_to_pnat m with
            | None => Some POne
            | Some p => Some (PS p)
            end
        end.
      
      (* Alternative: partial function for non-zero nats *)
      Fixpoint coq_nat_to_pnat_positive (n : nat) : PNat :=
        match n with
        | 0 => POne  (* Default to 1, but shouldn't be called with 0 *)
        | 1 => POne
        | S m => PS (coq_nat_to_pnat_positive m)
        end.
      
      (** ** The philosophical point *)
      Theorem what_are_numbers :
        forall n : PNat,
        (* Numbers are positive constructions beyond void *)
        (n = POne \/ exists m, n = PS m) /\
        (* All are equally impossible *)
        Is_Impossible (paradox_at n).
      Proof.
        intro n.
        split.
        - destruct n.
          + left. reflexivity.
          + right. exists n. reflexivity.
        - apply all_impossible.
      Qed.
      
      (* Zero is NOT a natural number - it's the void itself! *)
      Definition zero_is_void : Prop :=
        forall a : Alphacarrier, omega_veil a <-> False.
        
    End PureParadoxNaturals.
    
  End ParadoxNaturals.

  Module ParadoxIntegers.
    Import ParadoxNaturals.
    
    Section PureParadoxIntegers.
      Context {Alpha : AlphaType}.
      
      (* ================================================================ *)
      (** ** The Integer type *)
      
      Inductive PInt : Type :=
        | PZero : PInt               (* Zero: the void itself *)
        | PPos : PNat -> PInt        (* Positive: PPos POne = +1, PPos (PS POne) = +2 *)
        | PNeg : PNat -> PInt.       (* Negative: PNeg POne = -1, PNeg (PS POne) = -2 *)
      
      (* Map each integer to its paradox *)
      Definition int_paradox_at (i : PInt) : Alphacarrier -> Prop :=
        match i with
        | PZero => omega_veil                                    (* The void *)
        | PPos n => paradox_at n                                (* Forward construction *)
        | PNeg n => fun a => paradox_at n a /\ ~ paradox_at n a (* Self-contradiction *)
        end.
      
      (* All integer paradoxes are impossible *)
      Theorem all_int_impossible : forall i : PInt, 
        ImpossibilityAlgebra.Core.Is_Impossible (int_paradox_at i).
      Proof.
        intro i.
        destruct i; intro a.
        -
          split; intro H; exact H.
        -
          apply all_impossible.
        -
          split.
          + intros [H1 H2]. exfalso. exact (H2 H1).
          + intro H. exfalso. 
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
      Qed.
      
      (** ** Arithmetic Operations *)
      
      (* Negation *)
      Definition pint_neg (i : PInt) : PInt :=
        match i with
        | PZero => PZero
        | PPos n => PNeg n
        | PNeg n => PPos n
        end.
      
      (* Successor and predecessor *)
      Definition pint_succ (i : PInt) : PInt :=
        match i with
        | PZero => PPos POne           (* 0 + 1 = 1 *)
        | PPos n => PPos (PS n)        (* positive + 1 *)
        | PNeg POne => PZero           (* -1 + 1 = 0 *)
        | PNeg (PS n) => PNeg n        (* negative + 1 *)
        end.
      
      Definition pint_pred (i : PInt) : PInt :=
        match i with
        | PZero => PNeg POne           (* 0 - 1 = -1 *)
        | PNeg n => PNeg (PS n)        (* negative - 1 *)
        | PPos POne => PZero           (* 1 - 1 = 0 *)
        | PPos (PS n) => PPos n        (* positive - 1 *)
        end.
      
      (* Helper: add a positive natural to an integer *)
      Fixpoint add_pos_pnat (n : PNat) (j : PInt) : PInt :=
        match n with
        | POne => pint_succ j
        | PS n' => pint_succ (add_pos_pnat n' j)
        end.
      
      (* Helper: subtract a positive natural from an integer *)
      Fixpoint add_neg_pnat (n : PNat) (j : PInt) : PInt :=
        match n with
        | POne => pint_pred j
        | PS n' => pint_pred (add_neg_pnat n' j)
        end.
      
      (* Addition *)
      Definition pint_add (i j : PInt) : PInt :=
        match i with
        | PZero => j
        | PPos n => add_pos_pnat n j
        | PNeg n => add_neg_pnat n j
        end.
      
      (* Multiplication *)
      Definition pint_mult (i j : PInt) : PInt :=
        match i, j with
        | PZero, _ => PZero              (* void * anything = void *)
        | _, PZero => PZero              (* anything * void = void *)
        | PPos m, PPos n => PPos (mult m n)   (* No encoding issues! *)
        | PPos m, PNeg n => PNeg (mult m n)   
        | PNeg m, PPos n => PNeg (mult m n)   
        | PNeg m, PNeg n => PPos (mult m n)   (* negative * negative = positive *)
        end.
      
      (* Test cases *)
      Example mult_one_one : pint_mult (PPos POne) (PPos POne) = PPos POne.
      Proof. reflexivity. Qed.  (* 1 * 1 = 1 *)
      
      Example mult_two_three : 
        pint_mult (PPos (PS POne)) (PPos (PS (PS POne))) = 
        PPos (PS (PS (PS (PS (PS POne))))).
      Proof. reflexivity. Qed.  (* 2 * 3 = 6 *)
      
      Example mult_neg_two_three :
        pint_mult (PNeg (PS POne)) (PPos (PS (PS POne))) = 
        PNeg (PS (PS (PS (PS (PS POne))))).
      Proof. reflexivity. Qed.  (* -2 * 3 = -6 *)
      
      (** ** Properties *)
      
      Theorem neg_involutive : forall i : PInt,
        pint_neg (pint_neg i) = i.
      Proof.
        intro i.
        destruct i; reflexivity.
      Qed.
      
      Theorem succ_pred : forall i : PInt,
        pint_pred (pint_succ i) = i.
      Proof.
        intro i.
        destruct i; try reflexivity.
        destruct p; reflexivity.
      Qed.
      
      Theorem pred_succ : forall i : PInt,
        pint_succ (pint_pred i) = i.
      Proof.
        intro i.
        destruct i; try reflexivity.
        destruct p; reflexivity.
      Qed.
      
      (** ** Connection to Coq integers *)
      
      Open Scope Z_scope.
      
      Definition pint_to_Z (i : PInt) : Z :=
        match i with
        | PZero => 0
        | PPos n => Z.of_nat (pnat_to_coq_nat n)
        | PNeg n => Z.opp (Z.of_nat (pnat_to_coq_nat n))
        end.
      
      (* The philosophical point *)
      Theorem integers_are_signed_constructions :
        forall i : PInt,
        ImpossibilityAlgebra.Core.Is_Impossible (int_paradox_at i) /\
        (i = PZero \/ exists n : PNat, i = PPos n \/ i = PNeg n).
      Proof.
        intro i.
        split.
        - apply all_int_impossible.
        - destruct i.
          + left. reflexivity.
          + right. exists p. left. reflexivity.
          + right. exists p. right. reflexivity.
      Qed.
      
    End PureParadoxIntegers.
    
  End ParadoxIntegers.

  Module ParadoxRationals.
    Import ParadoxNaturals.
    Import ParadoxIntegers.
  
    Section PureParadoxRationals.
      Context {Alpha : AlphaType}.
      
      (** ** Rationals with 0 denominators allowed - because we handle paradox already anyway *)
      
      Definition PRat := (PInt * PInt)%type.
      
      (* Map rationals to their paradox *)
      Definition rat_paradox_at (r : PRat) : Alphacarrier -> Prop :=
        let (p, q) := r in
        match q with
        | PZero => omega_veil  (* Division by zero IS the void! *)
        | _ => int_paradox_at p  (* Otherwise, use numerator's paradox *)
        end.
      
      (* All rational paradoxes are impossible *)
      Theorem all_rat_impossible : forall r : PRat,
        ImpossibilityAlgebra.Core.Is_Impossible (rat_paradox_at r).
      Proof.
        intro r. destruct r as [p q].
        destruct q; simpl.
        - (* q = PZero: division by zero *)
          intro a. split; intro H; exact H.
        - (* q = PPos n *)
          apply all_int_impossible.
        - (* q = PNeg n *)
          apply all_int_impossible.
      Qed.
      
      (** ** Equivalence that Handles Division by Zero *)
      Definition rat_equiv (r1 r2 : PRat) : Prop :=
        let (p1, q1) := r1 in
        let (p2, q2) := r2 in
        match q1, q2 with
        | PZero, PZero => True  (* x/0 and y/0 - all infinities extensionally equal *)
        | PZero, _ => False
        | _, PZero => False
        | _, _ => pint_mult p1 q2 = pint_mult p2 q1
        end.
      
      (* Equivalence is reflexive *)
      Theorem rat_equiv_refl : forall r : PRat,
        rat_equiv r r.
      Proof.
        intro r. destruct r as [p q].
        destruct q; simpl; reflexivity.
      Qed.
      
      (* The void absorbs everything *)
      Theorem void_absorbs_multiplication : forall p q : PInt,
        rat_equiv (pint_mult p PZero, PZero) (q, PZero).
      Proof.
        intros p q. simpl. exact I.
      Qed.
      
      (** ** Arithmetic Operations *)
      
      (* Addition: (a/b) + (c/d) = (ad + bc)/(bd) *)
      Definition rat_add (r1 r2 : PRat) : PRat :=
        let (a, b) := r1 in
        let (c, d) := r2 in
        match b, d with
        | PZero, _ => (PZero, PZero)  (* ∞ + anything = ∞ *)
        | _, PZero => (PZero, PZero)  (* anything + ∞ = ∞ *)
        | _, _ => (pint_add (pint_mult a d) (pint_mult b c), pint_mult b d)
        end.
      
      (* Multiplication: (a/b) * (c/d) = (ac)/(bd) *)
      Definition rat_mult (r1 r2 : PRat) : PRat :=
        let (a, b) := r1 in
        let (c, d) := r2 in
        (pint_mult a c, pint_mult b d).
      
      (* Division creates rationals! *)
      Definition make_rat (p q : PInt) : PRat := (p, q).
      
      (* ================================================================ *)
      (** ** The Amazing Properties of Void Division *)
      
      (* 0/0 is the primordial undefined - the pure void *)
      Definition undefined : PRat := (PZero, PZero).
      
      Theorem undefined_is_void : 
        rat_paradox_at undefined = omega_veil.
      Proof.
        reflexivity.
      Qed.
      
      (* Any number divided by zero gives void *)
      Theorem div_zero_is_void : forall p : PInt,
        rat_paradox_at (p, PZero) = omega_veil.
      Proof.
        intro p. reflexivity.
      Qed.
      
      (* The wonderful theorem: arithmetic with undefined *)
      Theorem undefined_arithmetic :
        (* undefined + anything = undefined *)
        (forall r : PRat, rat_equiv (rat_add undefined r) undefined) /\
        (* undefined * anything = undefined *)
        (forall r : PRat, rat_equiv (rat_mult undefined r) undefined).
      Proof.
        split.
        - (* Addition with undefined *)
          intro r. destruct r as [p q].
          destruct q; simpl; exact I.
        - (* Multiplication with undefined *)
          intro r. destruct r as [p q].
          unfold undefined, rat_mult. simpl.
          (* (PZero, PZero) always *)
          unfold rat_equiv. simpl. exact I.
      Qed.
      
      (* All "infinite" rationals are the same void *)
      Theorem all_infinities_equal : forall p q : PInt,
        p <> PZero -> q <> PZero ->
        rat_equiv (p, PZero) (q, PZero).
      Proof.
        intros p q Hp Hq.
        simpl. exact I.
      Qed.
      
      (* But 0/n and m/n (n≠0) can be different *)
      Theorem finite_rationals_distinct : 
        ~ rat_equiv (PZero, PPos POne) (PPos POne, PPos POne).
      Proof.
        simpl. intro H.
        (* 0 * 1 ≠ 1 * 1 *)
        discriminate H.
      Qed.
      
      (** ** The Deep Truth About Division by Zero *)
      
      (* Division by zero doesn't break mathematics - it reveals the void *)
      Theorem division_by_zero_is_safe :
        forall p : PInt,
        exists r : PRat,
        r = (p, PZero) /\
        ImpossibilityAlgebra.Core.Is_Impossible (rat_paradox_at r).
      Proof.
        intro p.
        exists (p, PZero).
        split.
        - reflexivity.
        - apply all_rat_impossible.
      Qed.
      
      (* The philosophical idea: undefined isn't scary *)
      Theorem undefined_is_just_another_void :
        rat_paradox_at undefined = omega_veil /\
        rat_paradox_at (PPos POne, PZero) = omega_veil /\
        rat_paradox_at (PNeg POne, PZero) = omega_veil /\
        (* All lead to the same place *)
        forall p q : PInt,
        rat_paradox_at (p, PZero) = rat_paradox_at (q, PZero).
      Proof.
        split; [|split; [|split]]; reflexivity.
      Qed.
      
      (** ** Reciprocals and the Beauty of 1/0 *)
      
      Definition rat_reciprocal (r : PRat) : PRat :=
        let (p, q) := r in (q, p).
      
      (* The reciprocal of zero is infinity, and vice versa! *)
      Theorem zero_infinity_duality :
        rat_reciprocal (PZero, PPos POne) = (PPos POne, PZero) /\
        rat_reciprocal (PPos POne, PZero) = (PZero, PPos POne).
      Proof.
        split; reflexivity.
      Qed.

      (* But both infinities are the same void *)
      Theorem reciprocal_of_zero_is_void :
        forall n : PInt,
        n <> PZero ->
        rat_paradox_at (rat_reciprocal (PZero, n)) = omega_veil.
      Proof.
        intros n Hn.
        simpl. reflexivity.
      Qed.
      
      (* The perfect symmetry: 0 and ∞ are dual faces of the void *)
      
    End PureParadoxRationals.
    
    (* ================================================================ *)
    (** ** Stress Test: Division by Zero Doesn't Break Mathematics! *)

    Section StressTest.
      Context {Alpha : AlphaType}.
      
      (* Convenient names for test values *)
      Definition zero_rat := (PZero, PPos POne).        (* 0/1 = 0 *)
      Definition one_rat := (PPos POne, PPos POne).     (* 1/1 = 1 *)
      Definition two_rat := (PPos (PS POne), PPos POne). (* 2/1 = 2 *)
      Definition neg_one_rat := (PNeg POne, PPos POne).  (* -1/1 = -1 *)
      Definition infinity := (PPos POne, PZero).         (* 1/0 = ∞ *)
      Definition neg_infinity := (PNeg POne, PZero).     (* -1/0 = -∞ *)
      Definition nan := undefined.                       (* 0/0 = NaN *)
      
      (* Test 1: All infinities are equal *)
      Example all_infinities_same :
        rat_equiv infinity neg_infinity /\
        rat_equiv infinity nan /\
        rat_equiv neg_infinity nan.
      Proof.
        split; [|split]; simpl; exact I.
      Qed.
      
      (* Test 2: Infinity absorbs addition *)
      Example infinity_plus_finite :
        rat_equiv (rat_add infinity one_rat) infinity /\
        rat_equiv (rat_add infinity two_rat) infinity /\
        rat_equiv (rat_add neg_infinity one_rat) neg_infinity.
      Proof.
        split; [|split]; simpl; exact I.
      Qed.
      
      (* Test 3: Infinity plus infinity *)
      Example infinity_plus_infinity :
        rat_equiv (rat_add infinity infinity) infinity /\
        rat_equiv (rat_add infinity neg_infinity) infinity /\
        rat_equiv (rat_add nan infinity) nan.
      Proof.
        split; [|split]; simpl; exact I.
      Qed.
      
      (* Test 4: Multiplication with infinity *)
      Example infinity_times_finite :
        rat_equiv (rat_mult infinity two_rat) infinity /\
        rat_equiv (rat_mult neg_infinity two_rat) neg_infinity /\
        rat_equiv (rat_mult infinity zero_rat) nan.  (* ∞ * 0 = 0/0 = NaN *)
      Proof.
        split; [|split]; simpl; exact I.
      Qed.
      
      (* Test 5: Chain operations don't explode *)
      Example complex_chain :
        let r1 := rat_add infinity one_rat in           (* ∞ + 1 = ∞ *)
        let r2 := rat_mult r1 two_rat in                (* ∞ * 2 = ∞ *)
        let r3 := rat_add r2 neg_infinity in            (* ∞ + (-∞) = ∞ *)
        rat_equiv r3 infinity.
      Proof.
        simpl. exact I.
      Qed.
      
      (* Test 6: Division creates infinities safely *)
      Example creating_infinities :
        rat_paradox_at (PPos POne, PZero) = omega_veil /\
        rat_paradox_at (PPos (PS POne), PZero) = omega_veil /\
        rat_paradox_at (PNeg POne, PZero) = omega_veil.
      Proof.
        split; [|split]; reflexivity.
      Qed.
      
      (* Test 7: Reciprocals work correctly *)
      Example reciprocal_tests :
        rat_reciprocal infinity = (PZero, PPos POne) /\    (* 1/∞ = 0 *)
        rat_reciprocal zero_rat = infinity /\              (* 1/0 = ∞ *)
        rat_reciprocal nan = nan.                          (* 1/(0/0) = 0/0 *)
      Proof.
        split; [|split]; reflexivity.
      Qed.
      
      (* Test 8: Mixed finite/infinite arithmetic *)
      Example mixed_arithmetic :
        let r1 := rat_add one_rat two_rat in              (* 1 + 2 = 3 *)
        let r2 := rat_add r1 infinity in                  (* 3 + ∞ = ∞ *)
        let r3 := rat_mult two_rat one_rat in             (* 2 * 1 = 2 *)
        let r4 := rat_mult r3 infinity in                 (* 2 * ∞ = ∞ *)
        rat_equiv r2 infinity /\ rat_equiv r4 infinity.
      Proof.
        split; simpl; exact I.
      Qed.
      
      (* Test 9: Zero times infinity gives NaN *)
      Example zero_times_infinity :
        rat_equiv (rat_mult zero_rat infinity) nan /\
        rat_equiv (rat_mult infinity zero_rat) nan.
      Proof.
        split; simpl; exact I.
      Qed.
      
      (* Test 10: The system remains consistent *)
      Theorem infinity_consistent :
        (* We can't prove false *)
        ~ (rat_equiv one_rat infinity) /\
        (* Finite rationals remain distinct *)
        ~ (rat_equiv one_rat two_rat) /\
        (* But all infinities collapse to one *)
        (forall p q : PInt, 
          p <> PZero -> q <> PZero ->
          rat_equiv (p, PZero) (q, PZero)).
      Proof.
        split; [|split].
        - (* one_rat is not equivalent to infinity *)
          simpl.
          intro H. exact H.
        - (* one_rat is not equivalent to two_rat *)
          simpl.
          unfold pint_mult. simpl.
          unfold mult. simpl.
          intro H. discriminate H.
        - (* All infinities are equal *)
          intros p q Hp Hq.
          simpl. exact I.
      Qed.
      
      (* Test 11: Arithmetic infinity axioms hold *)
      Example infinity_axioms :
        (* ∞ + x = ∞ for finite x *)
        (forall x : PInt, rat_equiv (rat_add infinity (x, PPos POne)) infinity) /\
        (* ∞ * x = ∞ for non-zero finite x *)
        (forall x : PInt, x <> PZero -> 
          rat_equiv (rat_mult infinity (x, PPos POne)) infinity).
      Proof.
        split.
        - intro x. simpl. exact I.
        - intros x Hx. simpl. 
          destruct x; simpl; exact I.
      Qed.
      
      (* The ultimate test: we can compute with infinity! *)
      Definition compute_with_infinity (r : PRat) : PRat :=
        let sum := rat_add r infinity in
        let prod := rat_mult sum two_rat in
        let final := rat_add prod one_rat in
        final.
      
      Example computation_works :
        rat_equiv (compute_with_infinity one_rat) infinity /\
        rat_equiv (compute_with_infinity infinity) infinity /\
        rat_equiv (compute_with_infinity nan) nan.
      Proof.
        split; [|split]; simpl; exact I.
      Qed.

      (* Example exploring how infinity interacts with different operations *)
      Example infinity_operation_chain :
        let step1 := rat_add one_rat two_rat in           (* 1 + 2 = 3 *)
        let step2 := rat_mult step1 two_rat in            (* 3 * 2 = 6 *)
        let step3 := rat_add step2 infinity in            (* 6 + ∞ = ∞ *)
        let step4 := rat_mult step3 neg_one_rat in        (* ∞ * (-1) = -∞ *)
        let step5 := rat_add step4 infinity in            (* -∞ + ∞ = ∞ *)
        rat_equiv step3 infinity /\
        rat_equiv step4 neg_infinity /\
        rat_equiv step5 infinity.
      Proof.
        split; [|split]; simpl; exact I.
      Qed.

      (* Example showing how NaN propagates differently than infinity *)
      Example nan_propagation :
        let nan_plus_one := rat_add nan one_rat in        (* NaN + 1 = NaN *)
        let nan_times_two := rat_mult nan two_rat in      (* NaN * 2 = NaN *)
        let inf_plus_one := rat_add infinity one_rat in   (* ∞ + 1 = ∞ *)
        let inf_times_two := rat_mult infinity two_rat in (* ∞ * 2 = ∞ *)
        rat_equiv nan_plus_one nan /\
        rat_equiv nan_times_two nan /\
        rat_equiv inf_plus_one infinity /\
        rat_equiv inf_times_two infinity.
      Proof.
        split; [|split; [|split]]; simpl; exact I.
      Qed.

      (* Example showing the "absorbing" property of infinity in detail *)
      Example infinity_absorbs_everything :
        let hundred := (PPos (PS (PS (PS POne))), PPos POne) in  (* 4/1 for simplicity *)
        let tiny := (PPos POne, PPos (PS (PS POne))) in          (* 1/3 *)
        let negative := (PNeg (PS POne), PPos POne) in            (* -2/1 *)
        (* Adding any finite number to infinity gives infinity *)
        rat_equiv (rat_add infinity hundred) infinity /\
        rat_equiv (rat_add infinity tiny) infinity /\
        rat_equiv (rat_add infinity negative) infinity /\
        (* But adding infinity to itself still gives infinity *)
        rat_equiv (rat_add infinity infinity) infinity /\
        (* And adding opposite infinities gives infinity (by our definition) *)
        rat_equiv (rat_add infinity neg_infinity) infinity.
      Proof.
        split; [|split; [|split; [|split]]]; simpl; exact I.
      Qed.

      (* Example exploring what happens with reciprocals and arithmetic *)
      Example reciprocal_arithmetic :
        let two_thirds := (PPos (PS POne), PPos (PS (PS POne))) in  (* 2/3 *)
        let three_halves := rat_reciprocal two_thirds in            (* 3/2 *)
        let product := rat_mult two_thirds three_halves in          (* (2/3)*(3/2) = 6/6 = 1 *)
        (* Now let's see what happens with infinity *)
        let inf_recip := rat_reciprocal infinity in                  (* 1/∞ = 0/1 *)
        let inf_times_recip := rat_mult infinity inf_recip in       (* ∞ * 0 = NaN *)
        (* The results *)
        rat_equiv product one_rat /\                                 (* Normal reciprocal multiplication gives 1 *)
        rat_equiv inf_recip zero_rat /\                             (* 1/∞ = 0 *)
        rat_equiv inf_times_recip nan.                              (* ∞ * 0 = NaN *)
      Proof.
        split; [|split].
        - simpl. unfold rat_equiv, pint_mult. simpl. 
          unfold mult. simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. exact I.
      Qed.

      (* Example showing how zero interacts with operations *)
      Example zero_behavior :
        let zero_plus_zero := rat_add zero_rat zero_rat in         (* 0 + 0 = 0 *)
        let zero_times_inf := rat_mult zero_rat infinity in        (* 0 * ∞ = NaN *)
        let zero_div_zero := (PZero, PZero) in                      (* 0/0 = NaN *)
        let zero_div_one := zero_rat in                             (* 0/1 = 0 *)
        let one_div_zero := infinity in                             (* 1/0 = ∞ *)
        (* Check the equivalences *)
        rat_equiv zero_plus_zero zero_rat /\
        rat_equiv zero_times_inf nan /\
        rat_equiv zero_div_zero nan /\
        rat_equiv one_div_zero infinity /\
        (* And that they're different when they should be *)
        ~(rat_equiv zero_rat infinity).
      Proof.
        split; [|split; [|split; [|split]]].
        - simpl. reflexivity.
        - simpl. exact I.
        - simpl. exact I.
        - simpl. exact I.
        - simpl. intro H. exact H.
      Qed.

      (* A more complex computation showing the consistency of the system *)
      Definition complex_calculation (a b c : PRat) : PRat :=
        let sum := rat_add a b in                    (* a + b *)
        let product := rat_mult sum c in             (* (a + b) * c *)
        let reciprocal := rat_reciprocal product in  (* 1/((a + b) * c) *)
        let final := rat_add reciprocal one_rat in   (* 1/((a + b) * c) + 1 *)
        final.

      Example calculation_showcase :
        (* Case 1: Pure finite arithmetic *)
        let finite_calc := 
          let a := rat_add two_rat one_rat in        (* 2 + 1 = 3 *)
          let b := rat_mult a two_rat in             (* 3 * 2 = 6 *)
          let c := rat_reciprocal b in               (* 1/6 *)
          c in
        
        (* Case 2: Infinity appears mid-calculation *)  
        let mid_infinity :=
          let a := rat_mult two_rat infinity in      (* 2 * ∞ = ∞ *)
          let b := rat_reciprocal a in               (* 1/∞ = 0 *)
          let c := rat_add b one_rat in              (* 0 + 1 = 1 *)
          c in
          
        (* Case 3: Creating infinity through division *)
        let created_infinity :=
          let a := rat_reciprocal zero_rat in        (* 1/0 = ∞ *)
          let b := rat_add a one_rat in              (* ∞ + 1 = ∞ *)
          b in
          
        (* Case 4: Zero times infinity gives NaN *)
        let zero_inf_nan :=
          let a := rat_mult zero_rat infinity in     (* 0 * ∞ = NaN *)
          let b := rat_add a one_rat in              (* NaN + 1 = NaN *)
          b in
          
        (* Verify the results *)
        (* finite_calc should be (1, 6) *)
        (let (p, q) := finite_calc in 
        match p, q with 
        | PPos POne, PPos (PS (PS (PS (PS (PS POne))))) => True
        | _, _ => False
        end) /\
        rat_equiv mid_infinity one_rat /\
        rat_equiv created_infinity infinity /\
        rat_equiv zero_inf_nan nan.
      Proof.
        split; [|split; [|split]].
        - simpl. exact I.
        - simpl. reflexivity.
        - simpl. exact I.
        - simpl. exact I.
      Qed.

      (* Example showing that our arithmetic laws still hold (where sensible) *)
      Example arithmetic_laws_with_infinity :
        (* Commutativity still works *)
        (rat_equiv (rat_add infinity one_rat) (rat_add one_rat infinity)) /\
        (rat_equiv (rat_mult infinity two_rat) (rat_mult two_rat infinity)) /\
        (* Identity elements work normally for finite numbers *)
        (rat_equiv (rat_add one_rat zero_rat) one_rat) /\
        (rat_equiv (rat_mult two_rat one_rat) two_rat) /\
        (* Infinity breaks some laws but in a consistent way *)
        (rat_equiv (rat_add infinity zero_rat) infinity) /\        (* ∞ + 0 = NaN (actually!) *)
        (rat_equiv (rat_mult infinity zero_rat) nan) /\            (* ∞ * 0 = NaN *)
        (rat_equiv (rat_mult infinity zero_rat) infinity).         (* And NaN ≡ ∞ in this system! *)
      Proof.
        split; [|split; [|split; [|split; [|split; [|split]]]]]; simpl.
        - exact I.
        - exact I.
        - reflexivity.
        - reflexivity.
        - exact I.
        - exact I.
        - exact I.
      Qed.

      (* Philosophical victory: undefined is just another number *)
      Theorem undefined_is_first_class :
        exists (add : PRat -> PRat -> PRat)
              (mult : PRat -> PRat -> PRat)
              (recip : PRat -> PRat),
        (* Operations are defined everywhere *)
        (forall r s : PRat, exists t : PRat, add r s = t) /\
        (forall r s : PRat, exists t : PRat, mult r s = t) /\
        (forall r : PRat, exists t : PRat, recip r = t) /\
        (* Including for undefined! *)
        (exists t : PRat, add undefined undefined = t) /\
        (exists t : PRat, mult undefined one_rat = t).
      Proof.
        exists rat_add, rat_mult, rat_reciprocal.
        split; [|split; [|split; [|split]]].
        - intros. exists (rat_add r s). reflexivity.
        - intros. exists (rat_mult r s). reflexivity.
        - intro. exists (rat_reciprocal r). reflexivity.
        - exists undefined. reflexivity.
        - exists undefined. reflexivity.
      Qed.
      
    End StressTest.
    
  End ParadoxRationals.

  (** Connection to Standard Rationals *)
  (* Importing QArith messes with the meaning of "0" in our other contexts. *)
  (* TODO: Move this and other Coq interfaces to an API file later. *)
  Module RationalsCoqInterface.
    Import ParadoxIntegers.
    Import ParadoxRationals.
    From Stdlib Require Import QArith.
    
    Definition rat_to_Q (r : PRat) : option Q :=
      let (p, q) := r in
      match q with
      | PZero => None  
      | _ => Some (Qmake (pint_to_Z p) (Z.to_pos (pint_to_Z q)))
      end.
  End RationalsCoqInterface.
End ParadoxNumbers.