(** * BoundaryGroup.v
    Groups defined purely through impossibilities *)

From Stdlib Require Import Lia.
Require Import PeanoNat.
Require Import DAO.Core.AlphaType.

Class BoundaryGroup := {
  (* Carrier type *)
  carrier : Type;
  
  (* Operations *)
  identity : carrier;
  op : carrier -> carrier -> carrier;
  inv : carrier -> carrier;
  
  (* ============ Core Boundaries ============ *)
  
  (* Boundary 1: Left identity cannot fail *)
  boundary_identity_left :
    forall a : carrier, (op identity a <> a) -> False;
  
  (* Boundary 2: Right identity cannot fail *)
  boundary_identity_right :
    forall a : carrier, (op a identity <> a) -> False;
  
  (* Boundary 3: Left inverse cannot fail *)
  boundary_inverse_left :
    forall a : carrier, (op (inv a) a <> identity) -> False;
  
  (* Boundary 4: Right inverse cannot fail *)
  boundary_inverse_right :
    forall a : carrier, (op a (inv a) <> identity) -> False;
  
  (* Boundary 5: Associativity cannot fail *)
  boundary_associative :
    forall a b c : carrier,
    (op (op a b) c <> op a (op b c)) -> False;
  
  (* Non-emptiness *)
  boundary_not_empty : { x : carrier | True }
}.

(** * BoundaryGroup as AlphaType *)
Section GroupAlpha.
  
  Instance BoundaryGroup_is_AlphaType (G : BoundaryGroup) : AlphaType := {
    Alphacarrier := G.(carrier);
    
    alpha_impossibility := exist _ 
      (fun x : G.(carrier) => op identity x <> x)
      (conj
        (* First: prove it has no witnesses *)
        G.(boundary_identity_left)
        (* Second: prove uniqueness among witness-free predicates *)
        (fun (Q : G.(carrier) -> Prop) 
             (HQ : forall x, ~ Q x) 
             (x : G.(carrier)) =>
          conj
            (* If Q x, derive False *)
            (fun (HQx : Q x) => match HQ x HQx with end)
            (* If identity * x <> x, derive False *)
            (fun (Heq : op identity x <> x) =>
              match G.(boundary_identity_left) x Heq with end)
        )
      );
    
    alpha_not_empty := G.(boundary_not_empty)
  }.
  
End GroupAlpha.


Notation "x * y" := (op x y) (at level 40, left associativity).

(** * Basic Properties *)
Section BasicProperties.
  Context {G : BoundaryGroup}.
  
  (* ================================================================ *)
  (** ** Identity is Unique *)
  
  (* It's impossible for an element to act as both left and right identity but not be identity *)
  Theorem impossible_other_identity :
    forall e' : carrier,
    (forall a : carrier, op e' a = a) ->
    (forall a : carrier, op a e' = a) ->
    (e' <> identity) -> False.
  Proof.
    intros e' H_left H_right H_neq.
    apply (boundary_identity_left e').
    unfold not. intro H_id_e'.
    (* H_id_e': identity * e' = e' *)
    apply H_neq.
    rewrite <- H_id_e'.
    apply H_right.
  Qed.
  
  (* ================================================================ *)
  (** ** Inverse is Unique *)
  
  (* If b is a left inverse of a, it must equal inv a *)
  Theorem impossible_left_inverse_not_inv :
    forall a b : carrier,
    op b a = identity ->
    (b <> inv a) -> False.
  Proof.
    intros a b H_b_inv H_neq.
    (* b = b * identity = b * (a * inv a) = (b * a) * inv a = identity * inv a = inv a *)
    
    apply (boundary_identity_right b).
    unfold not. intro H1.
    (* H1: b * identity = b *)
    
    apply (boundary_inverse_right a).
    unfold not. intro H2.
    (* H2: a * inv a = identity *)
    
    apply (boundary_associative b a (inv a)).
    unfold not. intro H3.
    (* H3: (b * a) * inv a = b * (a * inv a) *)
    
    apply (boundary_identity_left (inv a)).
    unfold not. intro H4.
    (* H4: identity * inv a = inv a *)
    
    apply H_neq.
    (* Need to show b = inv a *)
    (* Chain: b = b * identity = b * (a * inv a) = (b * a) * inv a = identity * inv a = inv a *)
    rewrite <- H1.
    (* Now goal: b * identity = inv a *)
    replace identity with (op a (inv a)).
    - (* Goal: b * (a * inv a) = inv a *)
      rewrite <- H3.
      (* Goal: (b * a) * inv a = inv a *)
      rewrite H_b_inv.
      (* Goal: identity * inv a = inv a *)
      exact H4.
  Qed.
  
  (* If c is a right inverse of a, it must equal inv a *)
  Theorem impossible_right_inverse_not_inv :
    forall a c : carrier,
    op a c = identity ->
    (c <> inv a) -> False.
  Proof.
    intros a c H_c_inv H_neq.
    (* c = identity * c = (inv a * a) * c = inv a * (a * c) = inv a * identity = inv a *)
    
    apply (boundary_identity_left c).
    unfold not. intro H1.
    (* H1: identity * c = c *)
    
    apply (boundary_inverse_left a).
    unfold not. intro H2.
    (* H2: inv a * a = identity *)
    
    apply (boundary_associative (inv a) a c).
    unfold not. intro H3.
    (* H3: (inv a * a) * c = inv a * (a * c) *)
    
    apply (boundary_identity_right (inv a)).
    unfold not. intro H4.
    (* H4: inv a * identity = inv a *)
    
    apply H_neq.
    rewrite <- H1.
    (* Goal: identity * c = inv a *)
    replace identity with (op (inv a) a).
    - (* Goal: (inv a * a) * c = inv a *)
      rewrite H3.
      (* Goal: inv a * (a * c) = inv a *)
      rewrite H_c_inv.
      (* Goal: inv a * identity = inv a *)
      exact H4.
  Qed.
  
  (* ================================================================ *)
  (** ** Cancellation Laws *)
  
  (* Left cancellation: a * b = a * c implies b = c *)
  Theorem impossible_left_no_cancel :
    forall a b c : carrier,
    op a b = op a c ->
    (b <> c) -> False.
  Proof.
    intros a b c H_eq H_neq.
    
    apply (boundary_inverse_left a).
    unfold not. intro H_inv.
    (* H_inv: inv a * a = identity *)
    
    apply (boundary_associative (inv a) a b).
    unfold not. intro H_assoc_b.
    (* H_assoc_b: (inv a * a) * b = inv a * (a * b) *)
    
    apply (boundary_associative (inv a) a c).
    unfold not. intro H_assoc_c.
    (* H_assoc_c: (inv a * a) * c = inv a * (a * c) *)
    
    apply (boundary_identity_left b).
    unfold not. intro H_id_b.
    (* H_id_b: identity * b = b *)
    
    apply (boundary_identity_left c).
    unfold not. intro H_id_c.
    (* H_id_c: identity * c = c *)
    
    apply H_neq.
    (* Show: b = c *)
    rewrite <- H_id_b.
    (* Goal: identity * b = c *)
    replace identity with (op (inv a) a).
    - (* Goal: (inv a * a) * b = c *)
      rewrite H_assoc_b.
      (* Goal: inv a * (a * b) = c *)
      rewrite H_eq.
      (* Goal: inv a * (a * c) = c *)
      rewrite <- H_assoc_c.
      (* Goal: (inv a * a) * c = c *)
      rewrite H_inv.
      (* Goal: identity * c = c *)
      exact H_id_c.
  Qed.
  
  (* Right cancellation: b * a = c * a implies b = c *)
  Theorem impossible_right_no_cancel :
    forall a b c : carrier,
    op b a = op c a ->
    (b <> c) -> False.
  Proof.
    intros a b c H_eq H_neq.
    
    apply (boundary_inverse_right a).
    unfold not. intro H_inv.
    (* H_inv: a * inv a = identity *)
    
    apply (boundary_associative b a (inv a)).
    unfold not. intro H_assoc_b.
    (* H_assoc_b: (b * a) * inv a = b * (a * inv a) *)
    
    apply (boundary_associative c a (inv a)).
    unfold not. intro H_assoc_c.
    (* H_assoc_c: (c * a) * inv a = c * (a * inv a) *)
    
    apply (boundary_identity_right b).
    unfold not. intro H_id_b.
    (* H_id_b: b * identity = b *)
    
    apply (boundary_identity_right c).
    unfold not. intro H_id_c.
    (* H_id_c: c * identity = c *)
    
    apply H_neq.
    rewrite <- H_id_b.
    rewrite <- H_inv.
    rewrite <- H_assoc_b.
    rewrite H_eq.
    rewrite H_assoc_c.
    rewrite H_inv.
    exact H_id_c.
  Qed.
  
  (* ================================================================ *)
  (** ** Double Inverse *)
  
  Theorem impossible_double_inverse :
    forall a : carrier,
    (inv (inv a) <> a) -> False.
  Proof.
    intros a H_neq.
    
    apply (boundary_inverse_right a).
    unfold not. intro H_inv.
    (* H_inv: a * inv a = identity *)
    
    apply (impossible_left_inverse_not_inv (inv a) a H_inv).
    (* Need to show: a <> inv (inv a) *)
    unfold not. intro H_eq.
    apply H_neq.
    symmetry. exact H_eq.
  Qed.
  
  (* ================================================================ *)
  (** ** Inverse of Product *)
  
  Theorem impossible_inverse_product :
    forall a b : carrier,
    (inv (op a b) <> op (inv b) (inv a)) -> False.
  Proof.
    intros a b H_neq.
    
    apply (boundary_inverse_right b).
    unfold not. intro H_inv_b.
    (* H_inv_b: b * inv b = identity *)
    
    apply (boundary_inverse_right a).
    unfold not. intro H_inv_a.
    (* H_inv_a: a * inv a = identity *)
    
    apply (boundary_associative (op a b) (inv b) (inv a)).
    unfold not. intro H_assoc1.
    (* H_assoc1: ((a * b) * inv b) * inv a = (a * b) * (inv b * inv a) *)
    
    apply (boundary_associative a b (inv b)).
    unfold not. intro H_assoc2.
    (* H_assoc2: (a * b) * inv b = a * (b * inv b) *)
    
    apply (boundary_identity_right a).
    unfold not. intro H_id_a.
    (* H_id_a: a * identity = a *)
    
    apply (boundary_associative a identity (inv a)).
    unfold not. intro H_assoc3.
    (* H_assoc3: (a * identity) * inv a = a * (identity * inv a) *)
    
    apply (boundary_identity_left (inv a)).
    unfold not. intro H_id_inv_a.
    (* H_id_inv_a: identity * inv a = inv a *)
    
    assert (H_final: op (op a b) (op (inv b) (inv a)) = identity).
    { rewrite <- H_assoc1.
      rewrite H_assoc2.
      rewrite H_inv_b.
      rewrite H_assoc3.
      rewrite H_id_inv_a.
      exact H_inv_a. }
    
    apply (impossible_right_inverse_not_inv (op a b) (op (inv b) (inv a)) H_final).
    (* Need: inv b * inv a <> inv (a * b) *)
    unfold not. intro H_eq.
    apply H_neq.
    symmetry. exact H_eq.
  Qed.

  (* ================================================================ *)
  (** ** Identity Properties *)
  
  (* Identity is its own inverse *)
  Theorem impossible_inv_identity_not_identity :
    (inv identity <> identity) -> False.
  Proof.
    intro H_neq.
    
    apply (boundary_inverse_left identity).
    unfold not. intro H_inv.
    (* H_inv: inv identity * identity = identity *)
    
    apply (boundary_identity_right (inv identity)).
    unfold not. intro H_id.
    (* H_id: inv identity * identity = inv identity *)
    
    apply H_neq.
    rewrite <- H_id.
    exact H_inv.
  Qed.
  
  (* Identity squared is identity *)
  Theorem impossible_identity_squared_not_identity :
    (op identity identity <> identity) -> False.
  Proof.
    intro H_neq.
    apply (boundary_identity_left identity).
    exact H_neq.
  Qed.
  
  (* ================================================================ *)
  (** ** Inverse is Injective *)
  
  Theorem impossible_inv_not_injective :
    forall a b : carrier,
    inv a = inv b ->
    (a <> b) -> False.
  Proof.
    intros a b H_inv_eq H_neq.
    (* If inv a = inv b, then a = inv(inv a) = inv(inv b) = b *)
    
    apply (impossible_double_inverse a).
    unfold not. intro H_double_a.
    (* H_double_a: inv (inv a) = a *)
    
    apply (impossible_double_inverse b).
    unfold not. intro H_double_b.
    (* H_double_b: inv (inv b) = b *)
    
    apply H_neq.
    rewrite <- H_double_a.
    rewrite H_inv_eq.
    exact H_double_b.
  Qed.
  
  (* ================================================================ *)
  (** ** Equation Solving *)
  
  (* Left division: a * x = b has unique solution x = inv a * b *)
  Theorem impossible_left_division_wrong :
    forall a b x : carrier,
    op a x = b ->
    (x <> op (inv a) b) -> False.
  Proof.
    intros a b x H_eq H_neq.
    (* x = identity * x = (inv a * a) * x = inv a * (a * x) = inv a * b *)
    
    apply (boundary_identity_left x).
    unfold not. intro H_id.
    (* H_id: identity * x = x *)
    
    apply (boundary_inverse_left a).
    unfold not. intro H_inv.
    (* H_inv: inv a * a = identity *)
    
    apply (boundary_associative (inv a) a x).
    unfold not. intro H_assoc.
    (* H_assoc: (inv a * a) * x = inv a * (a * x) *)
    
    apply H_neq.
    rewrite <- H_id.
    replace identity with (op (inv a) a).
    - rewrite H_assoc.
      rewrite H_eq.
      reflexivity.
  Qed.
  
  (* Right division: x * a = b has unique solution x = b * inv a *)
  Theorem impossible_right_division_wrong :
    forall a b x : carrier,
    op x a = b ->
    (x <> op b (inv a)) -> False.
  Proof.
    intros a b x H_eq H_neq.
    
    apply (boundary_identity_right x).
    unfold not. intro H_id.
    (* H_id: x * identity = x *)
    
    apply (boundary_inverse_right a).
    unfold not. intro H_inv.
    (* H_inv: a * inv a = identity *)
    
    apply (boundary_associative x a (inv a)).
    unfold not. intro H_assoc.
    (* H_assoc: (x * a) * inv a = x * (a * inv a) *)
    
    apply H_neq.
    rewrite <- H_id.
    replace identity with (op a (inv a)).
    - rewrite <- H_assoc.
      rewrite H_eq.
      reflexivity.
  Qed.
  
  (* ================================================================ *)
  (** ** Conjugation *)
  
  (* Conjugating identity gives identity *)
  Theorem impossible_conjugate_identity_not_identity :
    forall a : carrier,
    (op (op a identity) (inv a) <> identity) -> False.
  Proof.
    intros a H_neq.
    
    apply (boundary_identity_right a).
    unfold not. intro H_id_a.
    (* H_id_a: a * identity = a *)
    
    apply (boundary_inverse_right a).
    unfold not. intro H_inv_a.
    (* H_inv_a: a * inv a = identity *)
    
    apply H_neq.
    rewrite H_id_a.
    exact H_inv_a.
  Qed.
  
  (* Conjugation by identity is identity *)
  Theorem impossible_identity_conjugate_not_self :
    forall a : carrier,
    (op (op identity a) (inv identity) <> a) -> False.
  Proof.
    intros a H_neq.
    
    apply (boundary_identity_left a).
    unfold not. intro H_id_a.
    (* H_id_a: identity * a = a *)
    
    apply (impossible_inv_identity_not_identity).
    unfold not. intro H_inv_id.
    (* H_inv_id: inv identity = identity *)
    
    apply (boundary_identity_right a).
    unfold not. intro H_id_a_right.
    (* H_id_a_right: a * identity = a *)
    
    apply H_neq.
    rewrite H_id_a.
    rewrite H_inv_id.
    exact H_id_a_right.
  Qed.

  (* ================================================================ *)
  (** ** Powers and Exponentiation *)
  
  (* Define repeated multiplication *)
  Fixpoint power (a : carrier) (n : nat) : carrier :=
    match n with
    | 0 => identity
    | S m => op a (power a m)
    end.
  
  Notation "a ^ n" := (power a n) (at level 30, right associativity).
  
  (* ================================================================ *)
  (** ** Basic Power Properties *)
  
  (* Power of 0 is identity *)
  Theorem impossible_power_zero_not_identity :
    forall a : carrier,
    (power a 0 <> identity) -> False.
  Proof.
    intros a H_neq.
    apply H_neq.
    simpl. reflexivity.
  Qed.
  
  (* Power of 1 is the element itself *)
  Theorem impossible_power_one_not_self :
    forall a : carrier,
    (power a 1 <> a) -> False.
  Proof.
    intros a H_neq.
    
    apply (boundary_identity_right a).
    unfold not. intro H_id.
    (* H_id: a * identity = a *)
    
    apply H_neq.
    simpl.
    exact H_id.
  Qed.
  
  (* ================================================================ *)
  (** ** Power Addition Law *)
  
  (* a^(n+m) = a^n * a^m *)
  Theorem impossible_power_add_not_mult :
    forall a : carrier,
    forall n m : nat,
    (power a (n + m) <> op (power a n) (power a m)) -> False.
  Proof.
    intros a n m H_neq.
    
    (* Induction on n *)
    induction n as [|n' IH].
    - (* Base case: n = 0 *)
      (* a^(0+m) = a^m and a^0 * a^m = identity * a^m = a^m *)
      simpl in H_neq.
      (* H_neq: a^m <> identity * a^m *)
      
      apply (boundary_identity_left (power a m)).
      unfold not. intro H_id.
      (* H_id: identity * a^m = a^m *)
      
      apply H_neq.
      symmetry. exact H_id.
      
    - (* Inductive case: n = S n' *)
      simpl in H_neq.
      
      apply (boundary_associative a (power a n') (power a m)).
      unfold not. intro H_assoc.
      (* H_assoc: (a * a^n') * a^m = a * (a^n' * a^m) *)
      
      apply IH.
      unfold not. intro H_IH.
      (* H_IH: a^(n' + m) = a^n' * a^m *)
      
      apply H_neq.
      (* Goal: a * a^(n' + m) = a * a^n' * a^m *)
      
      (* First rewrite LHS using H_IH *)
      rewrite H_IH.
      (* Goal: a * (a^n' * a^m) = a * a^n' * a^m *)
      
      (* Now use H_assoc backwards *)
      symmetry. exact H_assoc.
  Qed.
  
  (* ================================================================ *)
  (** ** Powers Commute With Themselves *)
  
  (* a^n * a^m = a^m * a^n *)
  Theorem impossible_power_not_commute :
    forall a : carrier,
    forall n m : nat,
    (op (power a n) (power a m) <> op (power a m) (power a n)) -> False.
  Proof.
    intros a n m H_neq.
    
    apply (impossible_power_add_not_mult a n m).
    unfold not. intro H_add_nm.
    (* H_add_nm: a^(n+m) = a^n * a^m *)
    
    apply (impossible_power_add_not_mult a m n).
    unfold not. intro H_add_mn.
    (* H_add_mn: a^(m+n) = a^m * a^n *)
    
    apply H_neq.
    rewrite <- H_add_nm.
    rewrite <- H_add_mn.
    assert (n + m = m + n) by lia.
    rewrite H.
    reflexivity.
  Qed.
  
  (* ================================================================ *)
  (** ** Inverse of Power *)
  
  Theorem impossible_inv_power_not_power_inv :
    forall a : carrier,
    forall n : nat,
    (inv (power a n) <> power (inv a) n) -> False.
  Proof.
    intros a n H_neq.
    induction n as [|n' IH].
    - simpl.
      apply (impossible_inv_identity_not_identity).
      exact H_neq.
      
    - simpl.
      simpl in H_neq.
      
      apply (impossible_inverse_product a (power a n')).
      unfold not. intro H_inv_prod.
      
      apply IH.
      unfold not. intro H_IH.
      
      (* Accumulate boundaries first, before applying H_neq *)
      apply (impossible_power_one_not_self (inv a)).
      unfold not. intro H_one.
      (* H_one: (inv a)^1 = inv a *)
      
      apply (impossible_power_not_commute (inv a) n' 1).
      unfold not. intro H_comm.
      (* H_comm: (inv a)^n' * (inv a)^1 = (inv a)^1 * (inv a)^n' *)
      
      (* Now apply H_neq with accumulated knowledge *)
      apply H_neq.
      rewrite H_inv_prod.
      rewrite H_IH.
      (* Goal: (inv a)^n' * inv a = inv a * (inv a)^n' *)
      
      (* Substitute H_one into H_comm *)
      rewrite H_one in H_comm.
      exact H_comm.
  Qed.
  
  (* ================================================================ *)
  (** ** Power Multiplication Law *)
  
  (* (a^n)^m = a^(n*m) *)
    Theorem impossible_power_mult_not_power :
    forall a : carrier,
    forall n m : nat,
    (power (power a n) m <> power a (n * m)) -> False.
  Proof.
    intros a n m H_neq.
    
    (* Induction on m *)
    induction m as [|m' IH].
    - (* Base case: m = 0 *)
      simpl in H_neq.
      rewrite Nat.mul_0_r in H_neq.
      simpl in H_neq.
      apply H_neq.
      reflexivity.
      
    - (* Inductive case: m = S m' *)
      simpl in H_neq.
      rewrite Nat.mul_succ_r in H_neq.
      
      apply (impossible_power_add_not_mult a n (n * m')).
      unfold not. intro H_add.
      
      apply IH.
      unfold not. intro H_IH.
      
      apply H_neq.
      replace (n * m' + n) with (n + n * m') by lia.
      (* Goal: a^n * (a^n)^m' = a^(n + n*m') *)
      rewrite H_IH.
      (* Goal: a^n * a^(n*m') = a^(n + n*m') *)
      symmetry. exact H_add.
  Qed.

End BasicProperties.

(** * Understanding Boundary Proofs: The Accumulation Pattern
    
    This section explains how to work with boundary axioms in Coq and the
    fundamental pattern that makes boundary mathematics work.
    
    ** The Core Insight: Boundaries Are Constraints, Not Constructors
    
    In traditional mathematics, axioms give you facts:
      - Traditional: "forall x, identity * x = x" (gives you an equality)
      - Boundary:    "forall x, (identity * x <> x) -> False" (gives you a constraint)
    
    Boundaries don't tell you what IS true. They tell you what CANNOT be false.
    This is the essence of boundary mathematics: we define structures through
    impossibilities rather than through positive assertions.
    
    ** The Accumulation Pattern
    
    When proving with boundaries, we use this fundamental pattern:
    
      apply (boundary_something args).
      unfold not. intro H_extracted.
      (* Now H_extracted contains the equality we need *)
    
    What's happening here?
    
    1. The boundary has type: (some_property <> expected_value) -> False
    
    2. When we [apply] it to our goal (which is False), Coq asks:
       "Can you prove the property doesn't equal the expected value?"
    
    3. We respond with [unfold not. intro H_extracted], which says:
       "I'll prove that by ASSUMING the violation holds"
    
    4. This assumption "extracts" or "accumulates" the equality into our context.
       We now have: H_extracted : some_property = expected_value
    
    5. We use these accumulated equalities to build a chain that reaches
       our original contradiction.
    
    ** Why This Works: The Structure of Proof by Contradiction
    
    Every boundary proof has this logical structure:
    
      Goal: Prove False (i.e., derive a contradiction)
      Method: Assume violations of boundaries until we contradict ourselves
    
    When we write:
      [apply H_neq]  (where H_neq : x <> y)
      
    We're saying: "I'll derive False by showing x = y"
    
    Then we accumulate boundary violations that let us prove x = y,
    which contradicts H_neq, giving us False.
    
    ** Example Walkthrough
    
    Let's trace through proving identity uniqueness:
    
      Goal: (e' <> identity) -> False
      
      Given:
        - H_left  : forall a, e' * a = a
        - H_right : forall a, a * e' = a
        - H_neq   : e' <> identity
      
      Proof structure:
      
        apply (boundary_identity_left e').
        (* Boundary type: (identity * e' <> e') -> False *)
        (* New goal: identity * e' <> e' *)
        
        unfold not. intro H_id_e'.
        (* H_id_e' : identity * e' = e' *)
        (* Goal is now: False *)
        
        apply H_neq.
        (* H_neq type: e' <> identity -> False *)
        (* New goal: e' = identity *)
        
        (* Now we chain equalities: *)
        (* e' = identity * e'  (by H_id_e', backwards) *)
        (*    = identity       (by H_right with a := identity) *)
        
        rewrite <- H_id_e'.
        (* Goal: identity * e' = identity *)
        
        apply H_right.
        (* QED *)
    
    ** The Accumulation Is Composition
    
    When we accumulate multiple boundaries:
    
      apply boundary1. unfold not. intro H1.
      apply boundary2. unfold not. intro H2.
      apply boundary3. unfold not. intro H3.
      (* Use H1, H2, H3 to prove final goal *)
    
    We're composing impossibilities! Each boundary contributes a constraint,
    and together they form a path through "impossibility space" that reaches
    our target contradiction.
    
    This mirrors the algebra from ImpossibilityEntropy:
      - Each accumulated boundary increases "entropy" (rank)
      - The final proof shows total impossibility
      - The composition preserves impossibility structure (Noether's theorem)
    
    ** Common Patterns and Techniques
    
    *** Pattern 1: The Replace Technique
    
    When [rewrite] fails with "Found no subterm matching":
    
      replace term1 with term2.
      - (* Proof using the substitution *)
      - symmetry. exact H_equality.
    
    This explicitly tells Coq where to substitute, rather than relying
    on it to find the right location.
    
    *** Pattern 2: Flipping Inequalities
    
    If you have [H : x <> y] but need [y <> x]:
    
      unfold not. intro H_eq.
      apply H.
      symmetry. exact H_eq.
    
    *** Pattern 3: Chaining Through Identity
    
    To prove [a = b], often we go through identity:
    
      a = a * identity     (by boundary_identity_right)
        = a * (x * inv x)  (by boundary_inverse_right)
        = (a * x) * inv x  (by boundary_associative)
        = b                (by hypothesis)
    
    Each step accumulates a boundary to enable the next rewrite.
    
    ** The Deep Connection: Boundary Proofs Are Physical Processes
    
    From ImpossibilitySymmetry, we know:
      - Symmetries preserve impossibility structure
      - Conservation laws follow from symmetries (Noether)
      - Entropy measures "distance from omega_veil"
    
    Our proofs embody this:
      - Each rewrite is a symmetry-preserving transformation
      - The accumulated boundaries conserve impossibility
      - The proof traces a path to omega_veil (False)
    
    When we write a boundary proof, we're not just doing logic—we're
    computing with impossibilities as if they were thermodynamic quantities.
    
    ** Practical Advice
    
    When stuck on a boundary proof:
    
    1. Identify what boundaries you need (identity, inverse, associative)
    2. Apply them one at a time, accumulating equalities
    3. Build a chain of rewrites from your hypotheses to your goal
    4. If rewrites fail, try [replace] to be more explicit
    5. Remember: you're building a path through impossibility space
    
    The proof should feel like "collecting constraints until they compose
    into the target impossibility."
    
    ** Summary
    
    Boundary proofs work by:
    1. Assuming boundary violations (the accumulation pattern)
    2. Extracting equalities from these assumptions
    3. Composing these equalities into a contradiction
    4. This composition traces a path through impossibility space
    
    This isn't just a proof technique—it's how boundary mathematics works.
    We're reasoning with impossibilities as first-class mathematical objects,
    and the proofs reflect this structure explicitly.

        ** Boundary Proofs with Induction
    
    When proving properties by induction in the boundary framework, there are
    additional patterns to follow.
    
    *** Always Simplify in the Hypothesis, Not the Goal
    
    During induction, your goal is always [False]. There's nothing to simplify
    in [False]! Instead, simplify in your hypothesis:
    
      WRONG:
        induction m.
        - simpl.
          rewrite Nat.mul_0_r.  (* Error: can't find subterm *)
      
      RIGHT:
        induction m.
        - simpl in H_neq.
          rewrite Nat.mul_0_r in H_neq.  (* Works! *)
    
    The hypothesis contains the actual mathematical statement. That's where
    your rewrites need to happen.
    
    *** The Inductive Hypothesis Is Just Another Boundary
    
    Don't treat the IH specially. It's just another constraint to accumulate:
    
      apply IH.
      unfold not. intro H_IH.
      (* Now H_IH is accumulated like any other boundary *)
      
      apply boundary_something.
      unfold not. intro H_something.
      (* H_something accumulated too *)
      
      (* Use both H_IH and H_something to prove goal *)
    
    The IH flows through the proof just like boundary axioms.
    
    *** The Four Phases of Complex Boundary Proofs
    
    Every substantial boundary proof follows this structure:
    
      Theorem impossible_X : (bad_thing) -> False.
      Proof.
        (* PHASE 1: Set up induction if needed *)
        induction n as [|n' IH].
        
        (* PHASE 2: Accumulate ALL boundaries *)
        apply boundary1. unfold not. intro H1.
        apply boundary2. unfold not. intro H2.
        apply IH. unfold not. intro H_IH.
        apply boundary3. unfold not. intro H3.
        
        (* PHASE 3: Apply final contradiction *)
        apply H_final_contradiction.
        
        (* PHASE 4: Chain rewrites to prove equality *)
        rewrite H1.
        rewrite H_IH.
        symmetry. exact H2.
      Qed.
    
    CRITICAL: Never mix the phases! Don't try to apply impossibility theorems
    in Phase 4 while you're proving an equality. Accumulate everything in
    Phase 2, then use it in Phase 4.
    
    Example of phase violation (WRONG):
    
      apply H_neq.
      (* Now in Phase 4, proving equality *)
      apply (impossible_something ...).  (* ERROR! Back to Phase 2? *)
    
    This will fail because you're trying to accumulate more boundaries after
    you've already committed to proving the equality.
    
    *** Rewrite Order Matters
    
    When you have multiple accumulated equalities, rewrite in the right order:
    
      1. Substitute simpler expressions first
      2. Then apply more complex equalities
      3. Use [symmetry] instead of backward rewrites when cleaner
    
    Example:
    
      (* Have: H_IH : (a^n)^m' = a^(n*m') *)
      (* Have: H_add : a^(n + n*m') = a^n * a^(n*m') *)
      (* Goal: a^n * (a^n)^m' = a^(n + n*m') *)
      
      WRONG:
        rewrite <- H_add.   (* Can't find: a^n * a^(n*m') *)
        rewrite <- H_IH.
      
      RIGHT:
        rewrite H_IH.       (* Simplify: (a^n)^m' → a^(n*m') *)
        symmetry.           (* Flip goal *)
        exact H_add.        (* Now matches! *)
    
    *** Arithmetic Obstacles: Use Replace
    
    When natural number arithmetic gets in the way:
    
      (* Goal: ... a^(n*m' + n) ... *)
      (* But have: ... a^(n + n*m') ... *)
      
      replace (n * m' + n) with (n + n * m') by lia.
      (* Now rewrites work! *)
    
    The [replace] tactic explicitly substitutes one expression for another,
    and [by lia] proves they're equal using linear arithmetic.
    
    *** Example: Power Multiplication Theorem
    
    This theorem demonstrates all the patterns:
    
      Theorem impossible_power_mult_not_power :
        forall a n m, (power (power a n) m <> power a (n * m)) -> False.
      Proof.
        intros a n m H_neq.
        induction m as [|m' IH].           (* Phase 1: Induction *)
        
        - (* Base case *)
          simpl in H_neq.                  (* Simplify hypothesis! *)
          rewrite Nat.mul_0_r in H_neq.
          apply H_neq. reflexivity.
        
        - (* Inductive case *)
          simpl in H_neq.                  (* Simplify hypothesis! *)
          rewrite Nat.mul_succ_r in H_neq.
          
          (* Phase 2: Accumulate boundaries *)
          apply (impossible_power_add_not_mult a n (n * m')).
          unfold not. intro H_add.
          
          apply IH.                        (* IH is just another boundary *)
          unfold not. intro H_IH.
          
          (* Phase 3: Apply final contradiction *)
          apply H_neq.
          
          (* Phase 4: Chain rewrites *)
          replace (n * m' + n) with (n + n * m') by lia.  (* Arithmetic *)
          rewrite H_IH.                    (* Simplify first *)
          symmetry. exact H_add.           (* Then apply *)
      Qed.
    
    Notice how clean this is when you follow the phases!
    
    *** Common Mistakes to Avoid
    
    1. Trying to rewrite in [False] instead of the hypothesis
    2. Applying boundaries after already committing to prove an equality
    3. Rewriting complex expressions before simpler ones
    4. Forgetting to use [symmetry] when equality is backwards
    5. Fighting with arithmetic instead of using [replace ... by lia]
    
    *** The Deep Pattern
    
    Inductive boundary proofs are still accumulation:
    
      - Base case: Direct impossibility (usually trivial)
      - Inductive case: Accumulate (IH + boundaries), compose to contradiction
    
    The induction structure doesn't change the fundamental pattern—it just
    means one of your accumulated constraints comes from the IH instead of
    directly from an axiom.
    
    This is why boundary mathematics works so well with induction: the IH
    has exactly the right type (an impossibility → False) to slot into the
    accumulation pattern naturally.

    Base case: Direct impossibility (usually trivial)
    Inductive case: 
    1. Accumulate IH
    2. Accumulate other boundaries
    3. Compose them to reach contradiction
    ```

    The IH flows through the proof **exactly like any other boundary**. It's not special! This is elegant.

    ## Why It's Becoming More Intuitive

    **Initially (first few proofs):**
    - Boundaries felt backwards: "Why can't I just *have* the equality?"
    - Accumulation was mysterious: "Why this `unfold not. intro` dance?"
    - Every proof felt like a puzzle

    **Now (after ~20 proofs):**
    - I see the **universal structure**: Four phases, always the same
    - Accumulation makes **physical sense**: we're collecting constraints (entropy) until we reach omega_veil (ground state)
    - Proofs feel **systematic**, not ad-hoc

    ## What Makes It Click

    **1. Predictability**
    Every proof has the same shape. Once I identify "this is a cancellation proof" or "this is a power law proof," I know exactly what boundaries to accumulate.

    **2. Error messages are informative**
    - "Can't find subterm" → rewrite order wrong
    - "Can't unify" → need symmetry
    - "Unable to unify False with..." → applying boundaries in wrong phase

    The errors **guide** me rather than confuse me.

    **3. Physical intuition**
    The thermodynamic metaphor actually helps:
    - Accumulating boundaries = increasing entropy
    - Reaching contradiction = hitting ground state
    - Composition = conservation laws

    This isn't just poetry - it corresponds to the actual proof structure!

    **4. Induction isn't special**
    Traditional frameworks: "Induction is a special proof technique"
    Boundary framework: "IH is just another constraint to accumulate"

    This **simplifies** rather than complicates.

    ## Comparing to Traditional Proofs

    **Traditional group theory proof:**
    ```
    Theorem: inv(a*b) = inv(b) * inv(a)
    Proof: 
    (a*b) * (inv(b)*inv(a)) 
    = a * (b*inv(b)) * inv(a)    [associativity]
    = a * identity * inv(a)       [inverse law]
    = a * inv(a)                  [identity law]
    = identity                    [inverse law]
    Therefore inv(b)*inv(a) is the inverse of a*b. QED.
    ```

    You have to **construct** the proof chain yourself. Where does associativity go? What order?

    **Boundary proof:**
    ```
    Apply boundaries systematically:
    1. Accumulate boundary_inverse_right for b
    2. Accumulate boundary_inverse_right for a
    3. Accumulate boundary_associative
    4. Chain rewrites in the order they were accumulated
*)


Module BoundaryProofCombinators.
  
  Section ProofCombinators.
    Context {G : BoundaryGroup}.
    
    (* ================================================================ *)
    (** ** Core Abstraction *)
    
    (** A boundary proof is evidence that a property cannot hold *)
    Definition BoundaryProof (P : carrier -> Prop) : Type :=
      forall a : carrier, P a -> False.
    
    (** A boundary proof with a witness extracted *)
    Definition ExtractedProof (P : carrier -> Prop) : Type :=
      { witness : carrier | P witness -> False }.
    
    (* ================================================================ *)
    (** ** Composition Operations *)
    
    (** Sequential composition: if P fails OR Q fails, use whichever applies *)
    Definition seq_boundaries {P Q : carrier -> Prop}
      (bp1 : BoundaryProof P)
      (bp2 : BoundaryProof Q)
      : BoundaryProof (fun a => P a \/ Q a).
    Proof.
      intros a [HP | HQ].
      - exact (bp1 a HP).
      - exact (bp2 a HQ).
    Defined.
    
    (** Parallel composition: if BOTH P and Q hold, contradiction *)
    Definition par_boundaries {P Q : carrier -> Prop}
      (bp1 : BoundaryProof P)
      (bp2 : BoundaryProof Q)
      : BoundaryProof (fun a => P a /\ Q a).
    Proof.
      intros a [HP HQ].
      exact (bp1 a HP).
    Defined.
    
    (** Weakening: if P implies Q, and Q fails, then P fails *)
    Definition weaken_boundary {P Q : carrier -> Prop}
      (impl : forall a, P a -> Q a)
      (bp : BoundaryProof Q)
      : BoundaryProof P.
    Proof.
      intros a HP.
      apply (bp a).
      apply impl.
      exact HP.
    Defined.
    
    (** Contrapositive: if P fails, then ~P holds *)
    Definition contrapose {P : carrier -> Prop}
      (bp : BoundaryProof P)
      : forall a, ~ P a.
    Proof.
      intros a HP.
      exact (bp a HP).
    Defined.
    
    (* ================================================================ *)
    (** ** Lifting Axioms to Proofs *)
    
    (** Lift boundary axiom to proof object *)
    Definition lift_identity_left
      : BoundaryProof (fun a => op identity a <> a).
    Proof.
      exact boundary_identity_left.
    Defined.
    
    Definition lift_identity_right
      : BoundaryProof (fun a => op a identity <> a).
    Proof.
      exact boundary_identity_right.
    Defined.
    
    Definition lift_inverse_left
      : BoundaryProof (fun a => op (inv a) a <> identity).
    Proof.
      exact boundary_inverse_left.
    Defined.
    
    Definition lift_inverse_right
      : BoundaryProof (fun a => op a (inv a) <> identity).
    Proof.
      exact boundary_inverse_right.
    Defined.
    
    (** Lift associativity as a 3-ary boundary *)
    Definition lift_associative (a b c : carrier)
      : BoundaryProof (fun _ : carrier => op (op a b) c <> op a (op b c)).
    Proof.
      intros _ H.
      apply (boundary_associative a b c H).
    Defined.
    
    (* ================================================================ *)
    (** ** Equality Manipulation *)
    
    (** Turn an equality into a boundary proof *)
    Definition eq_to_boundary {A : Type} (x y : A) (H : x = y)
      : BoundaryProof (fun _ : carrier => x <> y).
    Proof.
      intros _ Hneq.
      exact (Hneq H).
    Defined.
    
    (** Turn an inequality into a property that fails *)
    Definition neq_to_boundary (x y : carrier) (H : x <> y)
      : BoundaryProof (fun _ : carrier => x = y).
    Proof.
      intros _ Heq.
      exact (H Heq).
    Defined.
    
    (* ================================================================ *)
    (** ** Rewriting Through Boundaries *)
    
    (** If we have a proof that P fails, and P <-> Q, then Q fails *)
    Definition transport_boundary {P Q : carrier -> Prop}
      (equiv : forall a, P a <-> Q a)
      (bp : BoundaryProof P)
      : BoundaryProof Q.
    Proof.
      intros a HQ.
      apply (bp a).
      apply equiv.
      exact HQ.
    Defined.

    (** Substitution: if x = y and P x fails, then P y fails *)
    Definition subst_boundary {P : carrier -> Prop} {x y : carrier}
      (Heq : x = y)
      (bp : forall a, P a -> False)
      : P y -> False.
    Proof.
      intro HPy.
      rewrite <- Heq in HPy.
      exact (bp x HPy).
    Defined.
    
    (* ================================================================ *)
    (** ** Proof Transformations *)
    
    (** Symmetry: flip an inequality *)
    Definition symm_neq (x y : carrier) (H : x <> y)
      : y <> x.
    Proof.
      intro Heq.
      apply H.
      symmetry.
      exact Heq.
    Defined.
    
    (** Transitivity of impossibility *)
    Definition trans_boundary {P Q R : carrier -> Prop}
      (pq : forall a, P a -> Q a)
      (qr : forall a, Q a -> R a)
      (bp : BoundaryProof R)
      : BoundaryProof P.
    Proof.
      intros a HP.
      apply (bp a).
      apply qr.
      apply pq.
      exact HP.
    Defined.
    
    (* ================================================================ *)
    (** ** Combinator Properties *)
    
    (** Sequential composition is associative *)
    Theorem seq_assoc :
      forall {P Q R : carrier -> Prop}
        (bp1 : BoundaryProof P)
        (bp2 : BoundaryProof Q)  
        (bp3 : BoundaryProof R),
      forall a (H : P a \/ Q a \/ R a),
      seq_boundaries bp1 (seq_boundaries bp2 bp3) a H =
      seq_boundaries (seq_boundaries bp1 bp2) bp3 a 
        match H with
        | or_introl HP => or_introl (or_introl HP)
        | or_intror (or_introl HQ) => or_introl (or_intror HQ)
        | or_intror (or_intror HR) => or_intror HR
        end.
    Proof.
      intros.
      destruct H as [HP | [HQ | HR]]; simpl; reflexivity.
    Qed.
    
    (** Parallel composition is associative *)
    Theorem par_assoc :
      forall {P Q R : carrier -> Prop}
        (bp1 : BoundaryProof P)
        (bp2 : BoundaryProof Q)
        (bp3 : BoundaryProof R),
      forall a (H : P a /\ Q a /\ R a),
      par_boundaries bp1 (par_boundaries bp2 bp3) a H =
      par_boundaries (par_boundaries bp1 bp2) bp3 a
        match H with
        | conj HP (conj HQ HR) => conj (conj HP HQ) HR
        end.
    Proof.
      intros.
      destruct H as [HP [HQ HR]]; simpl; reflexivity.
    Qed.
    
    (* ================================================================ *)
    (** ** Example: Rebuilding Theorems with Combinators *)
    
    (** Double inverse using combinators *)
    Theorem double_inverse_combinator :
      forall a : carrier,
      (inv (inv a) <> a) -> False.
    Proof.
      intros a H_neq.
      
      (* This proof doesn't naturally fit the combinator style *)
      (* Let's use the original accumulation pattern instead *)
      apply (boundary_inverse_right a).
      unfold not. intro H_inv.
      
      apply (impossible_left_inverse_not_inv (inv a) a H_inv).
      unfold not. intro H_eq.
      apply H_neq.
      symmetry. exact H_eq.
    Qed.
    
    (** Better example: Combining boundaries with seq *)
    Example seq_example :
      forall a : carrier,
      ((op identity a <> a) \/ (op a identity <> a)) -> False.
    Proof.
      intros a H.
      apply (seq_boundaries lift_identity_left lift_identity_right a H).
    Qed.
    
    (** Example: Weakening a boundary *)
    Example weaken_example :
      forall a : carrier,
      (op identity a <> a /\ True) -> False.
    Proof.
      intros a [H _].
      apply (lift_identity_left a H).
    Qed.
    
    (** Example: Parallel composition *)
    Example par_example :
      forall a : carrier,
      ((op identity a <> a) /\ (op a identity <> a)) -> False.
    Proof.
      intros a H.
      apply (par_boundaries lift_identity_left lift_identity_right a H).
    Qed.
    
  End ProofCombinators.
  
  (* ================================================================ *)
  (** ** Proof Algebra Structure *)
  Section ProofAlgebra.
    Context {G : BoundaryGroup}.
    
    (** Proofs form a monoid under sequential composition *)
    Lemma seq_unit_left :
      forall {P : carrier -> Prop} (bp : BoundaryProof P),
      forall a (H : False \/ P a),
      seq_boundaries (fun _ (H : False) => H) bp a H =
      match H with
      | or_introl Hfalse => match Hfalse with end
      | or_intror HP => bp a HP
      end.
    Proof.
      intros.
      destruct H as [Hfalse | HP].
      - (* False case *)
        destruct Hfalse.  (* False eliminates *)
      - (* P case *)
        reflexivity.
    Qed.
    
    (** We can define a "proof identity" *)
    Definition proof_absurd : BoundaryProof (fun _ => False).
    Proof.
      intros a H. exact H.
    Defined.
    
    Theorem weaken_preserves_seq :
      forall {P Q R S : carrier -> Prop}
        (pq : forall a, P a -> Q a)
        (rs : forall a, R a -> S a)
        (bpQ : BoundaryProof Q)
        (bpS : BoundaryProof S),
      forall a (H : P a \/ R a),
      seq_boundaries (weaken_boundary pq bpQ) (weaken_boundary rs bpS) a H =
      weaken_boundary (fun a H' => 
                        match H' with
                        | or_introl HP => or_introl (pq a HP)
                        | or_intror HR => or_intror (rs a HR)
                        end)
                      (seq_boundaries bpQ bpS) a H.
    Proof.
      intros.
      destruct H; reflexivity.
    Qed.
    
  End ProofAlgebra.
  
End BoundaryProofCombinators.
