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