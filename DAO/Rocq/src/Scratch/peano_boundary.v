(* Boundary-Based Peano Arithmetic - Minimal Start
   
   Let's build this up one axiom at a time, making sure each one
   has the form: forall x, F x -> False
*)

(* Basic structure *)
Parameter nat : Type.
Parameter O : nat.
Parameter S : nat -> nat.

(* We need at least one element - formulated as a boundary *)
(* "It is impossible for nat to be empty" *)
Definition nat_is_empty : Prop :=
  ~ exists x : nat, True.

Axiom impossible_nat_empty : nat_is_empty -> False.

(* ================================================================ *)
(** * Axiom 1: Zero is not a successor *)

(* Define the "bad" predicate: what would it mean for O to be a successor? *)
Definition zero_is_successor (n : nat) : Prop :=
  O = S n.

(* Now axiomatize that this is impossible *)
Axiom impossible_zero_is_successor :
  forall n : nat, zero_is_successor n -> False.

(* Note: We're NOT trying to prove O <> S n in the traditional sense.
   We're simply stating: "the boundary includes zero_is_successor" *)

(* ================================================================ *)
(** * Axiom 2: Successor collisions are impossible *)

(* Define the "bad" predicate: different numbers having the same successor *)
Definition successor_collision (n m : nat) : Prop :=
  S n = S m /\ n <> m.

(* Axiomatize that this is impossible *)
Axiom impossible_successor_collision :
  forall n m : nat, successor_collision n m -> False.

(* Note: We're NOT deriving S_injective in the traditional sense.
   We're stating: "the boundary includes successor_collision" *)

(* ================================================================ *)
(** * Axiom 3: Induction failures are impossible *)

(* Define the "bad" predicate: a property that holds at O, is preserved by S,
   but fails somewhere *)
Definition induction_failure (P : nat -> Prop) (n : nat) : Prop :=
  P O /\ (forall m : nat, P m -> P (S m)) /\ ~ P n.

(* Axiomatize that this is impossible *)
Axiom impossible_induction_failure :
  forall (P : nat -> Prop) (n : nat), induction_failure P n -> False.

(* Note: We're NOT deriving the induction principle in the traditional sense.
   We're stating: "the boundary includes induction_failure" *)

(* ================================================================ *)
(** * Questions:
    
    What can we actually PROVE in this framework?
    What does mathematics look like when it's all boundaries?
*)

(* ================================================================ *)
(** * Simple Concrete Boundaries *)

(* Theorem: It's impossible for S O to equal O *)
Theorem impossible_S_O_equals_O : (S O = O) -> False.
Proof.
  intro H.
  apply (impossible_zero_is_successor O).
  unfold zero_is_successor.
  symmetry.
  exact H.
Qed.

(* Theorem: It's impossible for S (S O) to equal O *)
Theorem impossible_S_S_O_equals_O : (S (S O) = O) -> False.
Proof.
  intro H.
  apply (impossible_zero_is_successor (S O)).
  unfold zero_is_successor.
  symmetry.
  exact H.
Qed.

(* General pattern: it's impossible for any S^n O to equal O *)
Theorem impossible_succ_n_O_equals_O : forall n : nat, (S n = O) -> False.
Proof.
  intros n H.
  apply (impossible_zero_is_successor n).
  unfold zero_is_successor.
  symmetry.
  exact H.
Qed.

(* ================================================================ *)
(** * What did we just prove?
    
    We proved that specific numbers can't equal zero.
    These are all instances of our boundary axiom.
    
    Next: Can we prove boundaries about equality between non-zero numbers?
*)

(* ================================================================ *)
(** * Proving Distinctness of Different Numbers *)

(* First, we can prove O ≠ S O directly from our boundary *)
Theorem O_neq_S_O : O <> S O.
Proof.
  unfold not.
  intro H.
  apply (impossible_zero_is_successor O).
  unfold zero_is_successor.
  exact H.
Qed.

(* Now we can prove S O ≠ S (S O) by COMBINING boundaries *)
Theorem impossible_S_O_equals_S_S_O : (S O = S (S O)) -> False.
Proof.
  intro H.
  apply (impossible_successor_collision O (S O)).
  unfold successor_collision.
  split.
  - exact H.
  - exact O_neq_S_O.
Qed.

(* ================================================================ *)
(** * Reflection
    
    This is interesting! We:
    1. Used one boundary (zero_is_successor) to establish O ≠ S O
    2. Combined it with another boundary (successor_collision) 
    3. Derived a new boundary (S O ≠ S (S O))
    
    The boundaries compose!
*)

(* ================================================================ *)
(** * Using the Induction Boundary *)

(* Let's prove: no number equals its own successor *)
(* Strategy: Use induction with P n := (n = S n) -> False *)

Theorem no_number_equals_own_successor : 
  forall n : nat, (n = S n) -> False.
Proof.
  intro n.
  (* We'll use induction. Define our predicate. *)
  set (P := fun m : nat => (m = S m) -> False).
  
  (* We need to show P n, i.e., (n = S n) -> False *)
  (* We'll show this is impossible to fail by using impossible_induction_failure *)
  
  (* First, let's prove the base case: P O *)
  assert (base : P O).
  { unfold P. intro H.
    (* We have O = S O, but this contradicts impossible_zero_is_successor *)
    apply (impossible_zero_is_successor O).
    unfold zero_is_successor.
    exact H. }
  
  (* Next, prove the inductive step: forall m, P m -> P (S m) *)
  assert (step : forall m : nat, P m -> P (S m)).
  { intros m IH.
    unfold P in *.
    intro H_succ.
    (* We have S m = S (S m) *)
    (* If m = S m, we'd have a contradiction by IH *)
    (* If m ≠ S m, we have a collision, contradicting impossible_successor_collision *)
    apply (impossible_successor_collision m (S m)).
    unfold successor_collision.
    split.
    - exact H_succ.
    - unfold not. intro H_eq.
      apply (IH H_eq). }
  
  (* Now we can apply impossible_induction_failure *)
  (* If P could fail at n, that would contradict our induction boundary *)
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure (fun m => (m = S m) -> False) n).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.

(* ================================================================ *)
(** * Reflection on Induction
    
    We just proved something NON-TRIVIAL using the induction boundary!
    
    The proof shows:
    1. Base case: O ≠ S O (from zero_is_successor boundary)
    2. Inductive step: if m ≠ S m, then S m ≠ S (S m) (from collision boundary)
    3. Conclusion: it's impossible for ANY n to equal S n (from induction boundary)
    
    This demonstrates that boundary mathematics can handle inductive reasoning!
*)

(* ================================================================ *)
(** * Addition as Boundaries *)

(* We introduce addition as a parameter *)
Parameter add : nat -> nat -> nat.
Notation "x + y" := (add x y).

(* Traditional axioms for addition:
   - n + 0 = n
   - n + S m = S (n + m)
   
   As boundaries: it's impossible for these to NOT hold *)

Definition add_zero_violation (n : nat) : Prop :=
  n + O <> n.

Axiom impossible_add_zero_violation :
  forall n : nat, add_zero_violation n -> False.

Definition add_succ_violation (n m : nat) : Prop :=
  n + S m <> S (n + m).

Axiom impossible_add_succ_violation :
  forall n m : nat, add_succ_violation n m -> False.

(* ================================================================ *)
(** * What can we prove about addition?
    
    Let's start simple and see what boundaries we can derive.
*)

(* First, a very simple fact: O + O ≠ S O *)
Theorem impossible_O_plus_O_equals_S_O : (O + O = S O) -> False.
Proof.
  intro H.
  assert (H_neq : O <> S O).
  { apply O_neq_S_O. }
  
  assert (H_violation : add_zero_violation O).
  { unfold add_zero_violation.
    unfold not. intro H_eq.
    rewrite H_eq in H.
    apply (H_neq H). }
  
  apply (impossible_add_zero_violation O H_violation).
Qed.

(* ================================================================ *)
(** * Deriving More Addition Boundaries *)

(* Theorem: S n + O can't equal O *)
Theorem impossible_S_n_plus_O_equals_O :
  forall n : nat, (S n + O = O) -> False.
Proof.
  intros n H.
  (* We know by add_zero_violation that S n + O ≠ S n is impossible *)
  (* We also know O ≠ S n *)
  (* If S n + O = O, then combined with O ≠ S n, we get S n + O ≠ S n *)
  (* But that's impossible! *)
  
  apply (impossible_add_zero_violation (S n)).
  unfold add_zero_violation.
  unfold not. intro H_eq.
  (* We have S n + O = S n and S n + O = O *)
  rewrite H_eq in H.
  (* So S n = O *)
  apply (impossible_zero_is_successor n).
  unfold zero_is_successor.
  symmetry. exact H.
Qed.

(* That worked! Now let's try with S m on the right *)
Theorem impossible_n_plus_S_m_equals_O :
  forall n m : nat, (n + S m = O) -> False.
Proof.
  intros n m H.
  (* By add_succ_violation, n + S m ≠ S (n + m) is impossible *)
  (* If n + S m = O, then S (n + m) = O *)
  (* But S (n + m) = O contradicts zero_is_successor *)
  
  apply (impossible_add_succ_violation n m).
  unfold add_succ_violation.
  unfold not. intro H_eq.
  (* We have n + S m = S (n + m) and n + S m = O *)
  rewrite H_eq in H.
  (* So S (n + m) = O *)
  apply (impossible_zero_is_successor (n + m)).
  unfold zero_is_successor.
  symmetry. exact H.
Qed.

(* ================================================================ *)
(** * Deriving New Boundaries from Existing Ones *)

(* Theorem: It's impossible for n + O to not equal n *)
Theorem impossible_add_O_neq : forall n : nat, (n + O <> n) -> False.
Proof.
  intros n H.
  (* H states that n + O ≠ n *)
  (* But this is exactly add_zero_violation! *)
  apply (impossible_add_zero_violation n).
  unfold add_zero_violation.
  exact H.
Qed.


(* Theorem: It's impossible for O + n to not equal n *)
Theorem impossible_O_add_neq : forall n : nat, (O + n <> n) -> False.
Proof.
  intro n.
  (* Define our induction predicate *)
  set (P := fun m : nat => (O + m <> m) -> False).
  
  (* Base case: (O + O ≠ O) -> False *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    apply (impossible_add_zero_violation O).
    unfold add_zero_violation.
    exact H_neq. }
  
  (* Inductive step: P m -> P (S m) *)
  assert (step : forall m : nat, P m -> P (S m)).
  { intros m IH.
    unfold P in *.
    intro H_neq.
    (* We have O + S m ≠ S m *)
    (* This will contradict add_succ_violation *)
    apply (impossible_add_succ_violation O m).
    unfold add_succ_violation.
    unfold not. intro H_eq.
    (* H_eq: O + S m = S (O + m) *)
    (* H_neq: O + S m ≠ S m *)
    rewrite H_eq in H_neq.
    (* Now: S (O + m) ≠ S m *)
    (* This means O + m ≠ m, which contradicts IH *)
    apply IH.
    unfold not. intro H_inner.
    apply H_neq.
    rewrite H_inner.
    reflexivity. }
  
  (* Apply induction boundary *)
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P n).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.



(* Theorem: It's impossible for S m + n to not equal S (m + n) *)
Theorem impossible_S_add_neq : 
  forall m n : nat, (S m + n <> S (m + n)) -> False.
Proof.
  intros m n.
  (* Induction on n *)
  set (P := fun k : nat => (S m + k <> S (m + k)) -> False).
  
  (* Base case: (S m + O ≠ S (m + O)) -> False *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    (* S m + O ≠ S (m + O) *)
    (* By add_zero_violation: S m + O = S m *)
    (* By add_zero_violation: m + O = m, so S (m + O) = S m *)
    (* Therefore S m = S m, contradiction with H_neq *)
    
    apply (impossible_add_zero_violation (S m)).
    unfold add_zero_violation.
    unfold not. intro H_eq1.
    (* H_eq1: S m + O = S m *)
    apply (impossible_add_zero_violation m).
    unfold add_zero_violation.
    unfold not. intro H_eq2.
    (* H_eq2: m + O = m *)
    apply H_neq.
    rewrite H_eq1.
    rewrite H_eq2.
    reflexivity. }
  
  (* Inductive step: P k -> P (S k) *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    (* We have S m + S k ≠ S (m + S k) *)
    (* By add_succ_violation: S m + S k = S (S m + k) *)
    (* By add_succ_violation: m + S k = S (m + k) *)
    (* So: S (S m + k) ≠ S (S (m + k)) *)
    (* By successor collision: S m + k ≠ S (m + k) *)
    (* This contradicts IH! *)
    
    apply (impossible_add_succ_violation (S m) k).
    unfold add_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: S m + S k = S (S m + k) *)
    apply (impossible_add_succ_violation m k).
    unfold add_succ_violation.
    unfold not. intro H_eq2.
    (* H_eq2: m + S k = S (m + k) *)
    rewrite H_eq1 in H_neq.
    rewrite H_eq2 in H_neq.
    (* Now: S (S m + k) ≠ S (S (m + k)) *)
    (* This implies S m + k ≠ S (m + k) by successor collision *)
    apply IH.
    unfold not. intro H_inner.
    apply H_neq.
    rewrite H_inner.
    reflexivity. }
  
  (* Apply induction boundary *)
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P n).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* Theorem: It's impossible for addition to not commute *)
Theorem impossible_add_not_comm : 
  forall n m : nat, (n + m <> m + n) -> False.
Proof.
  intros n m.
  (* Induction on m, keeping n fixed *)
  set (P := fun k : nat => (n + k <> k + n) -> False).
  
  (* Base case: (n + O ≠ O + n) -> False *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    (* n + O = n by add_zero_violation *)
    (* O + n = n by O_add_neq *)
    (* Therefore n + O = O + n *)
    
    apply (impossible_add_zero_violation n).
    unfold add_zero_violation.
    unfold not. intro H_eq1.
    apply (impossible_O_add_neq n).
    unfold not. intro H_eq2.
    apply H_neq.
    rewrite H_eq1.
    rewrite H_eq2.
    reflexivity. }
  
  (* Inductive step: P k -> P (S k) *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    (* We have n + S k ≠ S k + n *)
    (* By add_succ_violation: n + S k = S (n + k) *)
    (* By impossible_S_add_neq: S k + n = S (k + n) *)
    (* So: S (n + k) ≠ S (k + n) *)
    (* This implies n + k ≠ k + n, contradicting IH *)
    
    apply (impossible_add_succ_violation n k).
    unfold add_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: n + S k = S (n + k) *)
    apply (impossible_S_add_neq k n).
    unfold not. intro H_eq2.
    (* H_eq2: S k + n = S (k + n) *)
    rewrite H_eq1 in H_neq.
    rewrite H_eq2 in H_neq.
    (* Now: S (n + k) ≠ S (k + n) *)
    (* Extract n + k ≠ k + n and apply IH *)
    apply IH.
    unfold not. intro H_inner.
    apply H_neq.
    rewrite H_inner.
    reflexivity. }
  
  (* Apply induction boundary *)
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P m).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* Theorem: It's impossible for addition to not be associative *)
Theorem impossible_add_not_assoc : 
  forall n m p : nat, ((n + m) + p <> n + (m + p)) -> False.
Proof.
  intros n m p.
  (* Induction on p *)
  set (P := fun k : nat => ((n + m) + k <> n + (m + k)) -> False).
  
  (* Base case: ((n + m) + O ≠ n + (m + O)) -> False *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    (* (n + m) + O = n + m by add_zero_violation *)
    (* m + O = m by add_zero_violation, so n + (m + O) = n + m *)
    (* Therefore they're equal *)
    
    apply (impossible_add_zero_violation (n + m)).
    unfold add_zero_violation.
    unfold not. intro H_eq1.
    apply (impossible_add_zero_violation m).
    unfold add_zero_violation.
    unfold not. intro H_eq2.
    apply H_neq.
    rewrite H_eq1.
    rewrite H_eq2.
    reflexivity. }
  
  (* Inductive step: P k -> P (S k) *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    (* We have (n + m) + S k ≠ n + (m + S k) *)
    (* By add_succ_violation: (n + m) + S k = S ((n + m) + k) *)
    (* By add_succ_violation: m + S k = S (m + k) *)
    (* So: n + (m + S k) = n + S (m + k) *)
    (* By add_succ_violation: n + S (m + k) = S (n + (m + k)) *)
    (* Therefore: S ((n + m) + k) ≠ S (n + (m + k)) *)
    (* This implies (n + m) + k ≠ n + (m + k), contradicting IH *)
    
    apply (impossible_add_succ_violation (n + m) k).
    unfold add_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: (n + m) + S k = S ((n + m) + k) *)
    apply (impossible_add_succ_violation m k).
    unfold add_succ_violation.
    unfold not. intro H_eq2.
    (* H_eq2: m + S k = S (m + k) *)
    apply (impossible_add_succ_violation n (m + k)).
    unfold add_succ_violation.
    unfold not. intro H_eq3.
    (* H_eq3: n + S (m + k) = S (n + (m + k)) *)
    rewrite H_eq1 in H_neq.
    rewrite H_eq2 in H_neq.
    rewrite H_eq3 in H_neq.
    (* Now: S ((n + m) + k) ≠ S (n + (m + k)) *)
    apply IH.
    unfold not. intro H_inner.
    apply H_neq.
    rewrite H_inner.
    reflexivity. }
  
  (* Apply induction boundary *)
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P p).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* ================================================================ *)
(** * Multiplication as Boundaries *)

(* We introduce multiplication as a parameter *)
Parameter mul : nat -> nat -> nat.
Notation "x * y" := (mul x y).

(* Traditional axioms for multiplication:
   - n × 0 = 0
   - n × S m = n × m + n
   
   As boundaries: it's impossible for these to NOT hold *)

Definition mul_zero_violation (n : nat) : Prop :=
  n * O <> O.

Axiom impossible_mul_zero_violation :
  forall n : nat, mul_zero_violation n -> False.

Definition mul_succ_violation (n m : nat) : Prop :=
  n * S m <> n * m + n.

Axiom impossible_mul_succ_violation :
  forall n m : nat, mul_succ_violation n m -> False.


(* Theorem: It's impossible for O * n to not equal O *)
Theorem impossible_O_mul_neq : forall n : nat, (O * n <> O) -> False.
Proof.
  intro n.
  set (P := fun k : nat => (O * k <> O) -> False).
  
  (* Base case *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    apply (impossible_mul_zero_violation O).
    unfold mul_zero_violation.
    exact H_neq. }
  
  (* Inductive step *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    (* O * S k ≠ O *)
    (* By mul_succ_violation: O * S k = O * k + O *)
    (* By O_add_neq: O * k + O = O * k *)
    (* By IH: O * k = O *)
    (* So O * S k = O, contradiction *)
    
    apply (impossible_mul_succ_violation O k).
    unfold mul_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: O * S k = O * k + O *)
    apply (impossible_add_zero_violation (O * k)).
    unfold add_zero_violation.
    unfold not. intro H_eq2.
    (* H_eq2: O * k + O = O * k *)
    rewrite H_eq1 in H_neq.
    rewrite H_eq2 in H_neq.
    (* Now: O * k ≠ O *)
    apply (IH H_neq). }
  
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P n).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* ================================================================ *)
(** * Simple Multiplication Properties *)

(* Define 1 *)
Definition one := S O.
Notation "1" := one.

(* Theorem: It's impossible for 1 * n to not equal n *)
Theorem impossible_one_mul_neq : forall n : nat, (1 * n <> n) -> False.
Proof.
  intro n.
  unfold one.
  set (P := fun k : nat => (S O * k <> k) -> False).
  
  (* Base case *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    apply (impossible_mul_zero_violation (S O)).
    unfold mul_zero_violation.
    exact H_neq. }
  
  (* Inductive step *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    
    apply (impossible_mul_succ_violation (S O) k).
    unfold mul_succ_violation.
    unfold not. intro H_eq.
    rewrite H_eq in H_neq.
    (* Now: S O * k + S O ≠ S k *)
    
    (* We need to show this leads to False *)
    (* S O * k + S O ≠ S k *)
    (* By IH: S O * k = k (in some sense) *)
    (* So: k + S O ≠ S k *)
    (* But k + S O = S (k + O) = S k, so this is impossible *)
    
    (* Problem: we can't extract k + S O = S k *)
    (* Let's work differently - show the contradiction more directly *)
    
    apply (impossible_add_succ_violation k O).
    unfold add_succ_violation.
    unfold not. intro H_succ.
    (* H_succ: k + S O = S (k + O) *)
    
    apply (impossible_add_zero_violation k).
    unfold add_zero_violation.
    unfold not. intro H_zero.
    (* H_zero: k + O = k *)
    
    apply IH.
    unfold not. intro H_inner.
    (* H_inner: S O * k = k *)
    
    apply H_neq.
    (* Need to show: S O * k + S O = S k *)
    (* We have: H_inner (S O * k = k), H_succ (k + S O = S (k + O)), H_zero (k + O = k) *)
    rewrite H_inner, H_succ, H_zero.
    reflexivity. }
  
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P n).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* Theorem: It's impossible for S m * n to not equal m * n + n *)
Theorem impossible_S_mul_neq : 
  forall m n : nat, (S m * n <> m * n + n) -> False.
Proof.
  intros m n.
  set (P := fun k : nat => (S m * k <> m * k + k) -> False).
  
  (* Base case *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    apply (impossible_mul_zero_violation (S m)).
    unfold mul_zero_violation.
    unfold not. intro H_eq1.
    apply (impossible_mul_zero_violation m).
    unfold mul_zero_violation.
    unfold not. intro H_eq2.
    apply (impossible_add_zero_violation O).
    unfold add_zero_violation.
    unfold not. intro H_eq3.
    apply H_neq.
    rewrite H_eq1, H_eq2, H_eq3.
    reflexivity. }
  
  (* Inductive step *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    
    (* Accumulate all the equalities we need *)
    apply (impossible_mul_succ_violation (S m) k).
    unfold mul_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: S m * S k = S m * k + S m *)
    
    apply (impossible_mul_succ_violation m k).
    unfold mul_succ_violation.
    unfold not. intro H_eq2.
    (* H_eq2: m * S k = m * k + m *)
    
    apply IH.
    unfold not. intro H_inner.
    (* H_inner: S m * k = m * k + k *)
    
    (* Now we need to show the rearrangement works *)
    (* Goal: (m * k + k) + S m = (m * k + m) + S k *)
    
    apply (impossible_add_not_assoc (m * k) k (S m)).
    unfold not. intro H_assoc1.
    (* H_assoc1: (m * k + k) + S m = m * k + (k + S m) *)
    
    apply (impossible_add_not_assoc (m * k) m (S k)).
    unfold not. intro H_assoc2.
    (* H_assoc2: (m * k + m) + S k = m * k + (m + S k) *)
    
    apply (impossible_add_succ_violation k m).
    unfold add_succ_violation.
    unfold not. intro H_succ1.
    (* H_succ1: k + S m = S (k + m) *)
    
    apply (impossible_add_succ_violation m k).
    unfold add_succ_violation.
    unfold not. intro H_succ2.
    (* H_succ2: m + S k = S (m + k) *)
    
    apply (impossible_add_not_comm k m).
    unfold not. intro H_comm.
    (* H_comm: k + m = m + k *)
    
    (* Now resolve H_neq using all accumulated equalities *)
    apply H_neq.
    rewrite H_eq1, H_eq2, H_inner, H_assoc1, H_assoc2, H_succ1, H_succ2, H_comm.
    reflexivity. }
  
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P n).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* Theorem: It's impossible for multiplication to not commute *)
Theorem impossible_mul_not_comm : 
  forall n m : nat, (n * m <> m * n) -> False.
Proof.
  intros n m.
  set (P := fun k : nat => (n * k <> k * n) -> False).
  
  (* Base case: (n * O ≠ O * n) -> False *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    apply (impossible_mul_zero_violation n).
    unfold mul_zero_violation.
    unfold not. intro H_eq1.
    apply (impossible_O_mul_neq n).
    unfold not. intro H_eq2.
    apply H_neq.
    rewrite H_eq1, H_eq2.
    reflexivity. }
  
  (* Inductive step: P k -> P (S k) *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    (* We have n * S k ≠ S k * n *)
    (* By mul_succ: n * S k = n * k + n *)
    (* By S_mul: S k * n = k * n + n *)
    (* By IH: n * k = k * n *)
    (* So: k * n + n = k * n + n, which is reflexive *)
    
    apply (impossible_mul_succ_violation n k).
    unfold mul_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: n * S k = n * k + n *)
    
    apply (impossible_S_mul_neq k n).
    unfold not. intro H_eq2.
    (* H_eq2: S k * n = k * n + n *)
    
    apply IH.
    unfold not. intro H_inner.
    (* H_inner: n * k = k * n *)
    
    apply H_neq.
    rewrite H_eq1, H_eq2, H_inner.
    reflexivity. }
  
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P m).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* Theorem: It's impossible for left distributivity to fail *)
(* n * (m + p) = n * m + n * p *)
Theorem impossible_mul_add_not_distr_l : 
  forall n m p : nat, (n * (m + p) <> n * m + n * p) -> False.
Proof.
  intros n m p.
  set (P := fun k : nat => (n * (m + k) <> n * m + n * k) -> False).
  
  (* Base case: (n * (m + O) ≠ n * m + n * O) -> False *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    apply (impossible_add_zero_violation m).
    unfold add_zero_violation.
    unfold not. intro H_eq1.
    (* H_eq1: m + O = m *)
    
    apply (impossible_mul_zero_violation n).
    unfold mul_zero_violation.
    unfold not. intro H_eq2.
    (* H_eq2: n * O = O *)
    
    apply (impossible_add_zero_violation (n * m)).
    unfold add_zero_violation.
    unfold not. intro H_eq3.
    (* H_eq3: n * m + O = n * m *)
    
    apply H_neq.
    rewrite H_eq1, H_eq2, H_eq3.
    reflexivity. }
  
  (* Inductive step: P k -> P (S k) *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    (* n * (m + S k) ≠ n * m + n * S k *)
    (* By add_succ: m + S k = S (m + k) *)
    (* By mul_succ: n * S (m + k) = n * (m + k) + n *)
    (* By mul_succ: n * S k = n * k + n *)
    (* By IH: n * (m + k) = n * m + n * k *)
    (* So: n * m + n * k + n = n * m + (n * k + n) *)
    
    apply (impossible_add_succ_violation m k).
    unfold add_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: m + S k = S (m + k) *)
    
    apply (impossible_mul_succ_violation n (m + k)).
    unfold mul_succ_violation.
    unfold not. intro H_eq2.
    (* H_eq2: n * S (m + k) = n * (m + k) + n *)
    
    apply (impossible_mul_succ_violation n k).
    unfold mul_succ_violation.
    unfold not. intro H_eq3.
    (* H_eq3: n * S k = n * k + n *)
    
    apply IH.
    unfold not. intro H_inner.
    (* H_inner: n * (m + k) = n * m + n * k *)
    
    apply (impossible_add_not_assoc (n * m) (n * k) n).
    unfold not. intro H_assoc.
    (* H_assoc: (n * m + n * k) + n = n * m + (n * k + n) *)
    
    apply H_neq.
    rewrite H_eq1, H_eq2, H_eq3, H_inner, H_assoc.
    reflexivity. }
  
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P p).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* Theorem: It's impossible for right distributivity to fail *)
(* (m + p) * n = m * n + p * n *)
Theorem impossible_mul_add_not_distr_r : 
  forall m p n : nat, ((m + p) * n <> m * n + p * n) -> False.
Proof.
  intros m p n.
  intro H_neq.
  
  (* Accumulate the equalities we need *)
  apply (impossible_mul_not_comm (m + p) n).
  unfold not. intro H_comm1.
  (* H_comm1: (m + p) * n = n * (m + p) *)
  
  apply (impossible_mul_add_not_distr_l n m p).
  unfold not. intro H_distr.
  (* H_distr: n * (m + p) = n * m + n * p *)
  
  apply (impossible_mul_not_comm n m).
  unfold not. intro H_comm2.
  (* H_comm2: n * m = m * n *)
  
  apply (impossible_mul_not_comm n p).
  unfold not. intro H_comm3.
  (* H_comm3: n * p = p * n *)
  
  apply H_neq.
  rewrite H_comm1, H_distr, H_comm2, H_comm3.
  reflexivity.
Qed.


(* Theorem: It's impossible for multiplication to not be associative *)
Theorem impossible_mul_not_assoc : 
  forall n m p : nat, ((n * m) * p <> n * (m * p)) -> False.
Proof.
  intros n m p.
  set (P := fun k : nat => ((n * m) * k <> n * (m * k)) -> False).
  
  (* Base case: ((n * m) * O ≠ n * (m * O)) -> False *)
  assert (base : P O).
  { unfold P.
    intro H_neq.
    apply (impossible_mul_zero_violation (n * m)).
    unfold mul_zero_violation.
    unfold not. intro H_eq1.
    (* H_eq1: (n * m) * O = O *)
    
    apply (impossible_mul_zero_violation m).
    unfold mul_zero_violation.
    unfold not. intro H_eq2.
    (* H_eq2: m * O = O *)
    
    apply (impossible_mul_zero_violation n).
    unfold mul_zero_violation.
    unfold not. intro H_eq3.
    (* H_eq3: n * O = O *)
    
    apply H_neq.
    rewrite H_eq1, H_eq2, H_eq3.
    reflexivity. }
  
  (* Inductive step: P k -> P (S k) *)
  assert (step : forall k : nat, P k -> P (S k)).
  { intros k IH.
    unfold P in *.
    intro H_neq.
    (* (n * m) * S k ≠ n * (m * S k) *)
    (* By mul_succ: (n * m) * S k = (n * m) * k + (n * m) *)
    (* By mul_succ: m * S k = m * k + m *)
    (* So: n * (m * S k) = n * (m * k + m) *)
    (* By distributivity: n * (m * k + m) = n * (m * k) + n * m *)
    (* By IH: (n * m) * k = n * (m * k) *)
    (* So both sides equal: n * (m * k) + n * m *)
    
    apply (impossible_mul_succ_violation (n * m) k).
    unfold mul_succ_violation.
    unfold not. intro H_eq1.
    (* H_eq1: (n * m) * S k = (n * m) * k + (n * m) *)
    
    apply (impossible_mul_succ_violation m k).
    unfold mul_succ_violation.
    unfold not. intro H_eq2.
    (* H_eq2: m * S k = m * k + m *)
    
    apply (impossible_mul_add_not_distr_l n (m * k) m).
    unfold not. intro H_distr.
    (* H_distr: n * (m * k + m) = n * (m * k) + n * m *)
    
    apply IH.
    unfold not. intro H_inner.
    (* H_inner: (n * m) * k = n * (m * k) *)
    
    apply H_neq.
    rewrite H_eq1, H_eq2, H_distr, H_inner.
    reflexivity. }
  
  unfold P.
  intro H_fails.
  apply (impossible_induction_failure P p).
  unfold induction_failure.
  split. exact base.
  split. exact step.
  unfold not. intro H_holds.
  apply (H_holds H_fails).
Qed.


(* ================================================================ *)
(** * Number Theory via Boundaries *)

(* Define divisibility as a boundary concept *)
(* "n divides m" means: it's impossible for all k to satisfy n * k ≠ m *)

(* First, let's define what it means for something to NOT divide *)
Definition does_not_divide (n m : nat) : Prop :=
  forall k : nat, n * k <> m.

(* Now we can talk about divisibility violations *)
Definition divisibility_claim (n m : nat) : Prop :=
  exists k : nat, n * k = m.

(* A simple case: O does not divide any S n *)
Theorem impossible_O_divides_S_n : 
  forall n : nat, (exists k : nat, O * k = S n) -> False.
Proof.
  intros n [k H].
  (* We have O * k = S n *)
  apply (impossible_O_mul_neq k).
  unfold not. intro H_zero.
  (* H_zero: O * k = O *)
  rewrite H_zero in H.
  (* Now: O = S n *)
  apply (impossible_zero_is_successor n).
  unfold zero_is_successor.
  exact H.
Qed.


(* ================================================================ *)
(** * Ordering Relations via Double Negation *)

(* n ≤ m means: it's impossible that no witness exists *)
Definition le (n m : nat) : Prop :=
  (forall k : nat, n + k <> m) -> False.

Notation "n <= m" := (le n m).

(* n < m means n ≤ m and n ≠ m *)
Definition lt (n m : nat) : Prop :=
  (n <= m) /\ (n <> m).

Notation "n < m" := (lt n m).

(* Now let's prove theorems about impossible orderings *)

(* It's impossible for any n to be less than O *)
Theorem impossible_n_lt_O : forall n : nat, (n < O) -> False.
Proof.
  intros n [H_le H_neq].
  unfold le in H_le.
  (* H_le: (forall k, n + k <> O) -> False *)
  apply H_le.
  (* Show: forall k, n + k <> O *)
  intro k.
  unfold not.
  intro H_eq.
  (* H_eq: n + k = O *)
  
  (* We need to show this is impossible *)
  (* Use induction on k to show n + k = O is impossible for all k when n ≠ O *)
  set (P := fun m : nat => (n + m = O) -> False).
  
  apply (impossible_induction_failure P k).
  unfold induction_failure.
  split.
  - (* Base case: (n + O = O) -> False *)
    unfold P.
    intro H_base.
    apply (impossible_add_zero_violation n).
    unfold add_zero_violation.
    unfold not. intro H_zero.
    (* H_zero: n + O = n *)
    rewrite H_zero in H_base.
    (* n = O *)
    apply H_neq.
    exact H_base.
    
  - (* Now we need the step AND the failure *)
    split.
    + (* Step: P m -> P (S m) *)
      intros m IH.
      unfold P in *.
      intro H_step.
      (* n + S m = O *)
      apply (impossible_n_plus_S_m_equals_O n m H_step).
      
    + (* Show P doesn't fail at k *)
      unfold not. intro H_holds.
      unfold P in H_holds.
      apply (H_holds H_eq).
Qed.


(* Reflexivity: n ≤ n *)
Theorem le_refl : forall n : nat, n <= n.
Proof.
  intro n.
  unfold le.
  intro H.
  (* H: forall k, n + k ≠ n *)
  (* We'll derive False by showing n + O ≠ n is impossible *)
  apply (impossible_add_zero_violation n).
  unfold add_zero_violation.
  (* Now goal is: n + O ≠ n *)
  exact (H O).
Qed.


(* The key lemma we need *)
Lemma impossible_succ_sum_eq_base :
  forall n k : nat, S (n + k) = n -> False.
Proof.
  intros n k H.
  (* Induction on n with hypothesis H *)
  set (P := fun m : nat => S (m + k) = m -> False).
  
  apply (impossible_induction_failure P n).
  unfold induction_failure.
  split.
  - (* Base: S (O + k) = O -> False *)
    unfold P.
    intro H_base.
    apply (impossible_O_add_neq k).
    unfold not. intro H_zero.
    rewrite H_zero in H_base.
    (* S k = O *)
    apply (impossible_zero_is_successor k).
    unfold zero_is_successor.
    symmetry.
    exact H_base.
    
  - split.
    + (* Step: P m -> P (S m) *)
      intros m IH.
      unfold P in *.
      intro H_step.
      (* S (S m + k) = S m *)
      apply (impossible_S_add_neq m k).
      unfold not. intro H_succ.
      rewrite H_succ in H_step.
      (* S (S (m + k)) = S m *)
      apply (impossible_successor_collision (S (m + k)) m).
      unfold successor_collision.
      split.
      * exact H_step.
      * unfold not. intro H_eq.
        (* S (m + k) = m *)
        apply (IH H_eq).
        
    + unfold not. intro H_holds.
      unfold P in H_holds.
      apply (H_holds H).
Qed.

(* Now the main theorem *)
Theorem impossible_Sn_le_n : forall n : nat, (S n <= n) -> False.
Proof.
  intros n H_le.
  unfold le in H_le.
  apply H_le.
  intros k.
  unfold not. intro H_eq.
  apply (impossible_S_add_neq n k).
  unfold not. intro H_succ.
  rewrite H_succ in H_eq.
  apply (impossible_succ_sum_eq_base n k H_eq).
Qed.


(* ================================================================ *)
(** * The Boundary Mathematics Pattern *)

(* 1. **Axiomatize impossibilities** - state what can't happen
   
   2. **Use violations to force relationships** - when we have a violation 
      boundary saying "X ≠ Y is impossible", we can use that to connect X 
      and Y in proofs
   
   3. **Chain contradictions** - assume something, derive it leads to a 
      known boundary, conclude it's impossible
   
   4. **Accumulate boundaries** - each theorem adds a new impossibility 
      to our collection
   
   5. **The "Accumulate then Contradict" pattern** - when proving complex
      properties:
      - Apply impossibility lemmas with `unfold not. intro H` to collect
        the equalities they imply
      - Keep the final contradiction as your target
      - Use all collected equalities together in one rewrite chain
      - This avoids needing to extract equalities; instead we assume 
        impossibilities and show they lead to absurdity
   
   6. **Universal quantification of violations** - to express existential
      claims constructively:
      - Instead of "exists k, P(k)", use "(forall k, ~P(k)) -> False"
      - This is double negation: ~~(exists k, P(k))
      - Constructively provable without needing witnesses
      - Example: n ≤ m means "(forall k, n + k ≠ m) -> False"
   
   7. **Positive-looking statements from pure boundaries** - definitions
      using universal quantification of violations create statements that:
      - Read naturally (like "n ≤ n" or "p is prime")
      - Are actually boundaries under the hood
      - Can be proven constructively from impossibility axioms
      - Never extract witnesses, just prove universal failure is impossible
   
   The key insight is: **violation boundaries like `n + O ≠ n -> False` 
   act as bridges**. They let us say "if these two things were different, 
   that would be impossible, so they must behave the same way in our 
   reasoning."
   
   The deeper insight: **we never extract positive equalities**. Instead,
   we assume violations, collect what they would imply, and show those
   implications lead to contradictions. The equalities exist only within
   the proof of impossibility, never as standalone facts. This keeps the
   framework fully constructive.
   
   The profound insight: **double negation enables natural mathematical
   language while staying purely in boundaries**. By defining concepts as
   "impossibility of universal failure" rather than "existence of witness",
   we can write mathematics that looks traditional but is philosophically
   grounded entirely in impossibilities. The framework is boundaries all
   the way down, with no classical logic needed.
*)