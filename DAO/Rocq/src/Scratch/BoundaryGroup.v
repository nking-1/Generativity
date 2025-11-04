(** * BoundaryGroup.v
    Groups defined purely through impossibilities *)

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
*)