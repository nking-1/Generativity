(** * ParadoxNaturals.v
    
    Numbers as construction depths of paradoxes.
    All paradoxes equal omega_veil, but their construction history gives us arithmetic.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import ZArith.

Module ParadoxNumbers.
  Module ParadoxNaturals.
    Import ImpossibilityAlgebra Core.

    Section PureParadoxNaturals.
      Context {Alpha : AlphaType}.
      
      (* ================================================================ *)
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
      
      (* ================================================================ *)
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
      
      (* ================================================================ *)
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
      
      (* ================================================================ *)
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
      
      (* ================================================================ *)
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
      (** ** The Integer type - now with direct encoding! *)
      
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
        - (* PZero *)
          split; intro H; exact H.
        - (* PPos n *)
          apply all_impossible.
        - (* PNeg n *)
          split.
          + intros [H1 H2]. exfalso. exact (H2 H1).
          + intro H. exfalso. 
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
      Qed.
      
      (* ================================================================ *)
      (** ** Arithmetic Operations - now direct! *)
      
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
      
      (* Multiplication - NOW TRIVIAL! *)
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
      
      (* ================================================================ *)
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
      
      (* ================================================================ *)
      (** ** Connection to Coq integers *)
      
      Open Scope Z_scope.
      
      Definition pint_to_Z (i : PInt) : Z :=
        match i with
        | PZero => 0
        | PPos n => Z.of_nat (pnat_to_coq_nat n)
        | PNeg n => Z.opp (Z.of_nat (pnat_to_coq_nat n))
        end.
      
      (* The philosophical point: so much cleaner! *)
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
      
      (* ================================================================ *)
      (** ** Rationals with Zero Denominators Allowed! *)
      
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
      
      (* ================================================================ *)
      (** ** Equivalence that Handles Division by Zero *)
      
      Definition rat_equiv (r1 r2 : PRat) : Prop :=
        let (p1, q1) := r1 in
        let (p2, q2) := r2 in
        match q1, q2 with
        | PZero, PZero => True  (* All infinities are equal! *)
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
      
      (* ================================================================ *)
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
        (* undefined * anything = undefined ALWAYS! *)
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
      
      (* ================================================================ *)
      (** ** The Incredible Unification *)
      
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
      
      (* ================================================================ *)
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
      
      (* The philosophical culmination: undefined isn't scary *)
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
      
      (* ================================================================ *)
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
    
    Section Philosophy.
      Context {Alpha : AlphaType}.
      
      (** Rationals show us that "undefined" is not a bug but a feature.
          Division by zero doesn't break mathematics - it reveals that
          infinity is just another name for the void we've known all along.
          
          Every "dangerous" operation in mathematics is safe in AlphaType
          because danger IS the void, and the void is our foundation. *)
      
      Definition WhatAreRationals : Type :=
        { r : PRat & ImpossibilityAlgebra.Core.Is_Impossible (rat_paradox_at r) }.
      
      Definition WhatIsInfinity : Prop :=
        forall p : PInt, rat_paradox_at (p, PZero) = omega_veil.
      
      Definition WhatIsUndefined : Prop :=
        rat_paradox_at (PZero, PZero) = omega_veil /\
        (* And undefined arithmetic still works! *)
        exists (add : PRat -> PRat -> PRat),
        forall r, add (PZero, PZero) r = (PZero, PZero).
      
    End Philosophy.

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
          simpl. (* This gives us False *)
          intro H. exact H. (* False -> False *)
        - (* one_rat is not equivalent to two_rat *)
          simpl. (* This gives us pint_mult (PPos POne) (PPos POne) = pint_mult (PPos (PS POne)) (PPos POne) *)
          unfold pint_mult. simpl.
          unfold mult. simpl.
          (* Now we have PPos POne = PPos (PS POne) *)
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

  (* ================================================================ *)
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