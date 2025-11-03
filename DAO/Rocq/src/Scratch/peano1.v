(* Axiomatic Natural Numbers - Building Math from Scratch *)

(** * Basic Axioms *)

(* The type of natural numbers *)
Parameter nat : Type.

(* Zero *)
Parameter O : nat.

(* Successor function *)
Parameter S : nat -> nat.

(* Axiom: Successor is injective *)
Axiom S_injective : forall n m : nat, S n = S m -> n = m.

(* Axiom: Zero is not a successor *)
Axiom O_not_S : forall n : nat, O <> S n.

(* Axiom: Principle of induction *)
Axiom nat_ind : forall P : nat -> Prop,
  P O ->
  (forall n : nat, P n -> P (S n)) ->
  forall n : nat, P n.

(** * Addition *)

(* Define addition recursively *)
Parameter add : nat -> nat -> nat.

(* Base case: n + 0 = n *)
Axiom add_O_r : forall n : nat, add n O = n.

(* Recursive case: n + S m = S (n + m) *)
Axiom add_S_r : forall n m : nat, add n (S m) = S (add n m).

(* Notation for convenience *)
Notation "x + y" := (add x y).

(** * Basic Theorems to Prove *)

(* Theorem: 0 + n = n (left identity) *)
Theorem add_O_l : forall n : nat, O + n = n.
Proof.
  intro n.
  (* We'll use induction on n *)
  apply (nat_ind (fun n => O + n = n)).
  - (* Base case: O + O = O *)
    apply add_O_r.
  - (* Inductive case: O + n = n -> O + S n = S n *)
    intros n' IH.
    rewrite add_S_r.
    rewrite IH.
    reflexivity.
Qed.

(* Theorem: S m + n = S (m + n) (left successor) *)
Theorem add_S_l : forall m n : nat, S m + n = S (m + n).
Proof.
  intros m n.
  (* Induction on n *)
  apply (nat_ind (fun n => S m + n = S (m + n))).
  - (* Base case: S m + O = S (m + O) *)
    rewrite add_O_r.
    rewrite add_O_r.
    reflexivity.
  - (* Inductive case *)
    intros n' IH.
    rewrite add_S_r.
    rewrite add_S_r.
    rewrite IH.
    reflexivity.
Qed.

(* Theorem: Commutativity of addition *)
Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  (* Induction on m *)
  apply (nat_ind (fun m => n + m = m + n)).
  - (* Base case: n + O = O + n *)
    rewrite add_O_r.
    rewrite add_O_l.
    reflexivity.
  - (* Inductive case: n + m = m + n -> n + S m = S m + n *)
    intros m' IH.
    rewrite add_S_r.
    rewrite add_S_l.
    rewrite IH.
    reflexivity.
Qed.

(* Theorem: Associativity of addition *)
Theorem add_assoc : forall n m p : nat, (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  (* Induction on p *)
  apply (nat_ind (fun p => (n + m) + p = n + (m + p))).
  - (* Base case *)
    rewrite add_O_r.
    rewrite add_O_r.
    reflexivity.
  - (* Inductive case *)
    intros p' IH.
    rewrite add_S_r.
    rewrite add_S_r.
    rewrite add_S_r.
    rewrite IH.
    reflexivity.
Qed.

(** * Multiplication *)

(* Define multiplication *)
Parameter mul : nat -> nat -> nat.

(* Base case: n × 0 = 0 *)
Axiom mul_O_r : forall n : nat, mul n O = O.

(* Recursive case: n × S m = n × m + n *)
Axiom mul_S_r : forall n m : nat, mul n (S m) = add (mul n m) n.

(* Notation *)
Notation "x * y" := (mul x y).

(* Theorem: 0 × n = 0 *)
Theorem mul_O_l : forall n : nat, O * n = O.
Proof.
  intro n.
  apply (nat_ind (fun n => O * n = O)).
  - (* Base case *)
    apply mul_O_r.
  - (* Inductive case *)
    intros n' IH.
    rewrite mul_S_r.
    rewrite IH.
    rewrite add_O_l.
    reflexivity.
Qed.

(* Theorem: S m × n = m × n + n *)
Theorem mul_S_l : forall m n : nat, S m * n = m * n + n.
Proof.
  intros m n.
  apply (nat_ind (fun n => S m * n = m * n + n)).
  - (* Base case *)
    rewrite mul_O_r.
    rewrite mul_O_r.
    rewrite add_O_r.
    reflexivity.
  - (* Inductive case *)
    intros n' IH.
    rewrite mul_S_r.
    rewrite mul_S_r.
    rewrite IH.
    (* Goal: m * n' + m + S n' = m * n' + n' + S m *)
    rewrite add_S_r.
    rewrite add_S_r.
    (* Goal: S (m * n' + m + n') = S (m * n' + n' + m) *)
    (* Just need to show: m * n' + m + n' = m * n' + n' + m *)
    assert (H : m * n' + m + n' = m * n' + (m + n')).
    { rewrite add_assoc. reflexivity. }
    rewrite H.
    assert (H2 : m * n' + n' + m = m * n' + (n' + m)).
    { rewrite add_assoc. reflexivity. }
    rewrite H2.
    (* Now just need: m + n' = n' + m *)
    assert (H3 : m + n' = n' + m).
    { apply add_comm. }
    rewrite H3.
    reflexivity.
Qed.

(* Theorem: n × 1 = n (useful lemma) *)
(* First we need to define 1 *)
Definition one := S O.
Notation "1" := one.

Theorem mul_1_r : forall n : nat, n * 1 = n.
Proof.
  intro n.
  unfold one.
  rewrite mul_S_r.
  rewrite mul_O_r.
  rewrite add_O_l.
  reflexivity.
Qed.

(* Theorem: Commutativity of multiplication *)
Theorem mul_comm : forall n m : nat, n * m = m * n.
Proof.
  intros n m.
  apply (nat_ind (fun m => n * m = m * n)).
  - (* Base case *)
    rewrite mul_O_r.
    rewrite mul_O_l.
    reflexivity.
  - (* Inductive case *)
    intros m' IH.
    rewrite mul_S_r.
    rewrite mul_S_l.
    rewrite IH.
    reflexivity.
Qed.

(* Theorem: Left distributivity *)
Theorem mul_add_distr_l : forall n m p : nat, n * (m + p) = n * m + n * p.
Proof.
  intros n m p.
  apply (nat_ind (fun p => n * (m + p) = n * m + n * p)).
  - (* Base case *)
    rewrite add_O_r.
    rewrite mul_O_r.
    rewrite add_O_r.
    reflexivity.
  - (* Inductive case *)
    intros p' IH.
    rewrite add_S_r.
    rewrite mul_S_r.
    rewrite mul_S_r.
    rewrite IH.
    (* Need: n * m + n * p' + n = n * m + (n * p' + n) *)
    rewrite add_assoc.
    reflexivity.
Qed.

(* Theorem: Associativity of multiplication *)
Theorem mul_assoc : forall n m p : nat, (n * m) * p = n * (m * p).
Proof.
  intros n m p.
  apply (nat_ind (fun p => (n * m) * p = n * (m * p))).
  - (* Base case *)
    rewrite mul_O_r.
    rewrite mul_O_r.
    rewrite mul_O_r.
    reflexivity.
  - (* Inductive case *)
    intros p' IH.
    rewrite mul_S_r.
    rewrite mul_S_r.
    rewrite IH.
    rewrite mul_add_distr_l.
    reflexivity.
Qed.

(* Now prove boundaries as theorems from our positive axioms *)
Theorem impossible_O_equals_S : forall n : nat, (O = S n) -> False.
Proof.
  intros n H.
  apply (O_not_S n H).
Qed.

Theorem impossible_S_collision : 
  forall n m : nat, (S n = S m /\ n <> m) -> False.
Proof.
  intros n m [Heq Hneq].
  apply Hneq.
  apply (S_injective n m Heq).
Qed.

Theorem impossible_add_O_neq : forall n : nat, (n + O <> n) -> False.
Proof.
  intros n H.
  apply H.
  apply add_O_r.
Qed.

(* Summary of what we've proven! *)
(** 
   We've built up basic arithmetic from axioms and proven:
   - Addition is commutative and associative
   - 0 is the identity for addition
   - Multiplication is commutative and associative  
   - Multiplication distributes over addition
   - Basic properties about successors and zero
   
   All from just 6 axioms about natural numbers!
*)