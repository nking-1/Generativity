Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.

(* ================================================================ *)
(** * BoundaryNat: The Interface *)
(* We make an impossibility contract that any Nat carrier must behave. *)

Class BoundaryNat := {
  (* Carrier type *)
  carrier : Type;
  
  (* Basic operations *)
  zero : carrier;
  succ : carrier -> carrier;
  
  (* ============ Core Boundaries ============ *)
  
  (* Boundary 1: Zero is never a successor *)
  boundary_zero_not_succ : 
    forall n : carrier, (zero = succ n) -> False;
  
  (* Boundary 2: Successor is injective *)
  boundary_succ_injective :
    forall n m : carrier, (succ n = succ m /\ n <> m) -> False;
  
  (* Boundary 3: Induction cannot fail *)
  boundary_induction :
    forall (P : carrier -> Prop),
      P zero ->
      (forall n, P n -> P (succ n)) ->
      forall n, (~ P n) -> False;
  
  boundary_not_empty : { x : carrier | True }
}.

Instance BoundaryNat_is_AlphaType (BN : BoundaryNat) : AlphaType := {
  Alphacarrier := BN.(carrier);
  
  alpha_impossibility := exist _ 
    (fun x : BN.(carrier) => BN.(zero) = BN.(succ) x)
    (conj
      BN.(boundary_zero_not_succ)
      (fun (Q : BN.(carrier) -> Prop) 
           (HQ : forall x, ~ Q x) 
           (x : BN.(carrier)) =>
        conj
          (fun (HQx : Q x) => match HQ x HQx with end)
          (fun (Heq : BN.(zero) = BN.(succ) x) =>
            match BN.(boundary_zero_not_succ) x Heq with end)
      )
    );
  
  alpha_not_empty := BN.(boundary_not_empty)
}.

(* ================================================================ *)
(** * Addition Extension *)

Class BoundaryNatWithAdd (BN : BoundaryNat) := {
  (* Addition operation *)
  add : BN.(carrier) -> BN.(carrier) -> BN.(carrier);
  
  (* Addition boundaries *)
  boundary_add_zero :
    forall n : BN.(carrier), (add n BN.(zero) <> n) -> False;
    
  boundary_add_succ :
    forall n m : BN.(carrier), 
      (add n (BN.(succ) m) <> BN.(succ) (add n m)) -> False
}.

(* Notation that requires both instances *)
Notation "x + y" := (add x y) (at level 50, left associativity).

(* ================================================================ *)
(** * Multiplication Extension *)

Class BoundaryNatWithMul (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN) := {
  (* Multiplication operation *)
  mul : BN.(carrier) -> BN.(carrier) -> BN.(carrier);
  
  (* Multiplication boundaries *)
  boundary_mul_zero :
    forall n : BN.(carrier), (mul n BN.(zero) <> BN.(zero)) -> False;
    
  boundary_mul_succ :
    forall n m : BN.(carrier), 
      (mul n (BN.(succ) m) <> BNA.(add) (mul n m) n) -> False
}.

Notation "x * y" := (mul x y) (at level 40, left associativity).

(* ================================================================ *)
(** * Theorems Proven Generically *)

Section GenericTheorems.
  Context `{BoundaryNat}.
  
  (* All your existing theorems, but now generic over ANY BoundaryNat *)
  
  Theorem generic_zero_neq_succ_zero : zero <> succ zero.
  Proof.
    unfold not. intro H'.
    apply (boundary_zero_not_succ zero).
    exact H'.
  Qed.
  
  Theorem generic_no_number_equals_own_successor :
    forall n : carrier, (n = succ n) -> False.
  Proof.
    intro n.
    set (P := fun m => (m = succ m) -> False).
    
    assert (base : P zero).
    { unfold P. intro H'.
      apply (boundary_zero_not_succ zero H'). }
    
    assert (step : forall m, P m -> P (succ m)).
    { intros m IH. unfold P in *.
      intro H_succ.
      apply (boundary_succ_injective m (succ m)).
      split; [exact H_succ | unfold not; intro H_eq; apply (IH H_eq)]. }
    
    unfold P. intro H_fails.
    apply (boundary_induction P base step n).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
End GenericTheorems.

Section GenericAdditionTheorems.
  Context {BN : BoundaryNat}.
  Context {BNA : BoundaryNatWithAdd BN}.
  
  (* Helper: impossible for O + n to not equal n *)
  Theorem generic_O_add_neq : 
    forall n : BN.(carrier), (BNA.(add) BN.(zero) n <> n) -> False.
  Proof.
    intro n.
    set (P := fun m : BN.(carrier) => (BNA.(add) BN.(zero) m <> m) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNA.(boundary_add_zero) BN.(zero)).
      exact H_neq. }
    
    (* Inductive step *)
    assert (step : forall m : BN.(carrier), P m -> P (BN.(succ) m)).
    { intros m IH. unfold P in *.
      intro H_neq.
      apply (BNA.(boundary_add_succ) BN.(zero) m).
      unfold not. intro H_eq.
      rewrite H_eq in H_neq.
      apply IH.
      unfold not. intro H_inner.
      apply H_neq.
      rewrite H_inner.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step n).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  (* Helper: impossible for S m + n to not equal S (m + n) *)
  Theorem generic_S_add_neq :
    forall m n : BN.(carrier), 
      (BNA.(add) (BN.(succ) m) n <> BN.(succ) (BNA.(add) m n)) -> False.
  Proof.
    intros m n.
    set (P := fun k : BN.(carrier) => 
      (BNA.(add) (BN.(succ) m) k <> BN.(succ) (BNA.(add) m k)) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNA.(boundary_add_zero) (BN.(succ) m)).
      unfold not. intro H_eq1.
      apply (BNA.(boundary_add_zero) m).
      unfold not. intro H_eq2.
      apply H_neq.
      rewrite H_eq1, H_eq2.
      reflexivity. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNA.(boundary_add_succ) (BN.(succ) m) k).
      unfold not. intro H_eq1.
      apply (BNA.(boundary_add_succ) m k).
      unfold not. intro H_eq2.
      rewrite H_eq1 in H_neq.
      rewrite H_eq2 in H_neq.
      apply IH.
      unfold not. intro H_inner.
      apply H_neq.
      rewrite H_inner.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step n).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  Theorem generic_add_comm :
    forall n m : BN.(carrier), 
      (BNA.(add) n m <> BNA.(add) m n) -> False.
  Proof.
    intros n m.
    set (P := fun k : BN.(carrier) => 
      (BNA.(add) n k <> BNA.(add) k n) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNA.(boundary_add_zero) n).
      unfold not. intro H_eq1.
      apply (generic_O_add_neq n).
      unfold not. intro H_eq2.
      apply H_neq.
      rewrite H_eq1, H_eq2.
      reflexivity. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNA.(boundary_add_succ) n k).
      unfold not. intro H_eq1.
      apply (generic_S_add_neq k n).
      unfold not. intro H_eq2.
      rewrite H_eq1 in H_neq.
      rewrite H_eq2 in H_neq.
      apply IH.
      unfold not. intro H_inner.
      apply H_neq.
      rewrite H_inner.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step m).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  Theorem generic_add_assoc :
    forall n m p : BN.(carrier), 
      (BNA.(add) (BNA.(add) n m) p <> BNA.(add) n (BNA.(add) m p)) -> False.
  Proof.
    intros n m p.
    set (P := fun k : BN.(carrier) => 
      (BNA.(add) (BNA.(add) n m) k <> BNA.(add) n (BNA.(add) m k)) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNA.(boundary_add_zero) (BNA.(add) n m)).
      unfold not. intro H_eq1.
      apply (BNA.(boundary_add_zero) m).
      unfold not. intro H_eq2.
      apply H_neq.
      rewrite H_eq1, H_eq2.
      reflexivity. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNA.(boundary_add_succ) (BNA.(add) n m) k).
      unfold not. intro H_eq1.
      apply (BNA.(boundary_add_succ) m k).
      unfold not. intro H_eq2.
      apply (BNA.(boundary_add_succ) n (BNA.(add) m k)).
      unfold not. intro H_eq3.
      rewrite H_eq1 in H_neq.
      rewrite H_eq2 in H_neq.
      rewrite H_eq3 in H_neq.
      apply IH.
      unfold not. intro H_inner.
      apply H_neq.
      rewrite H_inner.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step p).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
End GenericAdditionTheorems.


Section GenericMultiplicationTheorems.
  Context {BN : BoundaryNat}.
  Context {BNA : BoundaryNatWithAdd BN}.
  Context {BNM : BoundaryNatWithMul BN BNA}.
  
  (* Helper: impossible for O * n to not equal O *)
  Theorem generic_O_mul_neq : 
    forall n : BN.(carrier), (BNM.(mul) BN.(zero) n <> BN.(zero)) -> False.
  Proof.
    intro n.
    set (P := fun k : BN.(carrier) => 
      (BNM.(mul) BN.(zero) k <> BN.(zero)) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNM.(boundary_mul_zero) BN.(zero)).
      exact H_neq. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNM.(boundary_mul_succ) BN.(zero) k).
      unfold not. intro H_eq1.
      apply (BNA.(boundary_add_zero) (BNM.(mul) BN.(zero) k)).
      unfold not. intro H_eq2.
      rewrite H_eq1 in H_neq.
      rewrite H_eq2 in H_neq.
      apply (IH H_neq). }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step n).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  (* Helper: Define 1 *)
  Definition one := BN.(succ) BN.(zero).
  
  (* Helper: impossible for 1 * n to not equal n *)
  Theorem generic_one_mul_neq : 
    forall n : BN.(carrier), (BNM.(mul) one n <> n) -> False.
  Proof.
    intro n.
    unfold one.
    set (P := fun k : BN.(carrier) => 
      (BNM.(mul) (BN.(succ) BN.(zero)) k <> k) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNM.(boundary_mul_zero) (BN.(succ) BN.(zero))).
      exact H_neq. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNM.(boundary_mul_succ) (BN.(succ) BN.(zero)) k).
      unfold not. intro H_eq.
      rewrite H_eq in H_neq.
      apply (BNA.(boundary_add_succ) k BN.(zero)).
      unfold not. intro H_succ.
      apply (BNA.(boundary_add_zero) k).
      unfold not. intro H_zero.
      apply IH.
      unfold not. intro H_inner.
      apply H_neq.
      rewrite H_inner, H_succ, H_zero.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step n).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  (* Helper: impossible for S m * n to not equal m * n + n *)
  Theorem generic_S_mul_neq :
    forall m n : BN.(carrier),
      (BNM.(mul) (BN.(succ) m) n <> BNA.(add) (BNM.(mul) m n) n) -> False.
  Proof.
    intros m n.
    set (P := fun k : BN.(carrier) => 
      (BNM.(mul) (BN.(succ) m) k <> BNA.(add) (BNM.(mul) m k) k) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNM.(boundary_mul_zero) (BN.(succ) m)).
      unfold not. intro H_eq1.
      apply (BNM.(boundary_mul_zero) m).
      unfold not. intro H_eq2.
      apply (BNA.(boundary_add_zero) BN.(zero)).
      unfold not. intro H_eq3.
      apply H_neq.
      rewrite H_eq1, H_eq2, H_eq3.
      reflexivity. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNM.(boundary_mul_succ) (BN.(succ) m) k).
      unfold not. intro H_eq1.
      apply (BNM.(boundary_mul_succ) m k).
      unfold not. intro H_eq2.
      apply IH.
      unfold not. intro H_inner.
      apply (generic_add_assoc (BNM.(mul) m k) k (BN.(succ) m)).
      unfold not. intro H_assoc1.
      apply (generic_add_assoc (BNM.(mul) m k) m (BN.(succ) k)).
      unfold not. intro H_assoc2.
      apply (BNA.(boundary_add_succ) k m).
      unfold not. intro H_succ1.
      apply (BNA.(boundary_add_succ) m k).
      unfold not. intro H_succ2.
      apply (generic_add_comm k m).
      unfold not. intro H_comm.
      apply H_neq.
      rewrite H_eq1, H_eq2, H_inner, H_assoc1, H_assoc2, H_succ1, H_succ2, H_comm.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step n).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  Theorem generic_mul_comm :
    forall n m : BN.(carrier), 
      (BNM.(mul) n m <> BNM.(mul) m n) -> False.
  Proof.
    intros n m.
    set (P := fun k : BN.(carrier) => 
      (BNM.(mul) n k <> BNM.(mul) k n) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNM.(boundary_mul_zero) n).
      unfold not. intro H_eq1.
      apply (generic_O_mul_neq n).
      unfold not. intro H_eq2.
      apply H_neq.
      rewrite H_eq1, H_eq2.
      reflexivity. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNM.(boundary_mul_succ) n k).
      unfold not. intro H_eq1.
      apply (generic_S_mul_neq k n).
      unfold not. intro H_eq2.
      rewrite H_eq1 in H_neq.
      rewrite H_eq2 in H_neq.
      apply IH.
      unfold not. intro H_inner.
      apply H_neq.
      rewrite H_inner.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step m).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  Theorem generic_mul_distrib_l :
    forall n m p : BN.(carrier), 
      (BNM.(mul) n (BNA.(add) m p) <> BNA.(add) (BNM.(mul) n m) (BNM.(mul) n p)) -> False.
  Proof.
    intros n m p.
    set (P := fun k : BN.(carrier) => 
      (BNM.(mul) n (BNA.(add) m k) <> BNA.(add) (BNM.(mul) n m) (BNM.(mul) n k)) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNA.(boundary_add_zero) m).
      unfold not. intro H_eq1.
      apply (BNM.(boundary_mul_zero) n).
      unfold not. intro H_eq2.
      apply (BNA.(boundary_add_zero) (BNM.(mul) n m)).
      unfold not. intro H_eq3.
      apply H_neq.
      rewrite H_eq1, H_eq2, H_eq3.
      reflexivity. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNA.(boundary_add_succ) m k).
      unfold not. intro H_eq1.
      apply (BNM.(boundary_mul_succ) n (BNA.(add) m k)).
      unfold not. intro H_eq2.
      apply (BNM.(boundary_mul_succ) n k).
      unfold not. intro H_eq3.
      apply IH.
      unfold not. intro H_inner.
      apply (generic_add_assoc (BNM.(mul) n m) (BNM.(mul) n k) n).
      unfold not. intro H_assoc.
      apply H_neq.
      rewrite H_eq1, H_eq2, H_eq3, H_inner, H_assoc.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step p).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
  Theorem generic_mul_distrib_r :
    forall m p n : BN.(carrier),
      (BNM.(mul) (BNA.(add) m p) n <> BNA.(add) (BNM.(mul) m n) (BNM.(mul) p n)) -> False.
  Proof.
    intros m p n H_neq.
    apply (generic_mul_comm (BNA.(add) m p) n).
    unfold not. intro H_comm1.
    apply (generic_mul_distrib_l n m p).
    unfold not. intro H_distr.
    apply (generic_mul_comm n m).
    unfold not. intro H_comm2.
    apply (generic_mul_comm n p).
    unfold not. intro H_comm3.
    apply H_neq.
    rewrite H_comm1, H_distr, H_comm2, H_comm3.
    reflexivity.
  Qed.
  
  Theorem generic_mul_assoc :
    forall n m p : BN.(carrier),
      (BNM.(mul) (BNM.(mul) n m) p <> BNM.(mul) n (BNM.(mul) m p)) -> False.
  Proof.
    intros n m p.
    set (P := fun k : BN.(carrier) => 
      (BNM.(mul) (BNM.(mul) n m) k <> BNM.(mul) n (BNM.(mul) m k)) -> False).
    
    (* Base case *)
    assert (base : P BN.(zero)).
    { unfold P. intro H_neq.
      apply (BNM.(boundary_mul_zero) (BNM.(mul) n m)).
      unfold not. intro H_eq1.
      apply (BNM.(boundary_mul_zero) m).
      unfold not. intro H_eq2.
      apply (BNM.(boundary_mul_zero) n).
      unfold not. intro H_eq3.
      apply H_neq.
      rewrite H_eq1, H_eq2, H_eq3.
      reflexivity. }
    
    (* Inductive step *)
    assert (step : forall k : BN.(carrier), P k -> P (BN.(succ) k)).
    { intros k IH. unfold P in *.
      intro H_neq.
      apply (BNM.(boundary_mul_succ) (BNM.(mul) n m) k).
      unfold not. intro H_eq1.
      apply (BNM.(boundary_mul_succ) m k).
      unfold not. intro H_eq2.
      apply (generic_mul_distrib_l n (BNM.(mul) m k) m).
      unfold not. intro H_distr.
      apply IH.
      unfold not. intro H_inner.
      apply H_neq.
      rewrite H_eq1, H_eq2, H_distr, H_inner.
      reflexivity. }
    
    unfold P. intro H_fails.
    apply (BN.(boundary_induction) P base step p).
    unfold not. intro H_holds.
    apply (H_holds H_fails).
  Qed.
  
End GenericMultiplicationTheorems.


(* ================================================================ *)
(** * Instance 1: Standard Coq nat *)

Require Import PeanoNat.

Instance StandardNat : BoundaryNat := {
  carrier := nat;
  zero := 0;
  succ := S;
  
  boundary_zero_not_succ := fun n H => 
    (* 0 = S n is impossible in standard nat *)
    match H in _ = s return match s with 0 => True | S _ => False end with
    | eq_refl => I
    end;
  
  boundary_succ_injective := fun n m H =>
    (* S n = S m /\ n <> m is impossible *)
    let (Heq, Hneq) := H in
    Hneq (f_equal pred Heq);
  
  boundary_induction := fun P H0 HS n Hn =>
    (* Induction principle *)
    Hn (nat_ind P H0 HS n);
  
  boundary_not_empty := exist _ 0 I
}.


Instance StandardNatAdd : BoundaryNatWithAdd StandardNat := {
  add := Nat.add;
  
  boundary_add_zero := fun n H =>
    H (Nat.add_0_r n);
  
  boundary_add_succ := fun n m H =>
    H (Nat.add_succ_r n m)
}.

Instance StandardNatMul : BoundaryNatWithMul StandardNat StandardNatAdd := {
  mul := Nat.mul;
  
  boundary_mul_zero := fun n H =>
    H (Nat.mul_0_r n);
  
  boundary_mul_succ := fun n m H =>
    H (Nat.mul_succ_r n m)
}.

(* ================================================================ *)
(** * Demonstrate that all generic theorems apply to standard nat *)

(* Example: commutativity holds for standard nat *)
Example standard_add_comm : 
  forall n m : nat, (n + m <> m + n) -> False.
Proof.
  apply (@generic_add_comm StandardNat StandardNatAdd).
Qed.

Example standard_mul_comm :
  forall n m : nat, (n * m <> m * n) -> False.
Proof.
  apply (@generic_mul_comm StandardNat StandardNatAdd StandardNatMul).
Qed.

Example standard_mul_distrib :
  forall n m p : nat, (n * (m + p) <> n * m + n * p) -> False.
Proof.
  apply (@generic_mul_distrib_l StandardNat StandardNatAdd StandardNatMul).
Qed.


(* ================================================================ *)
(** * Instance 2: List-based natural numbers *)

Require Import List.
Import ListNotations.

(* Natural numbers as lists of units *)
Instance ListNat : BoundaryNat := {
  carrier := list unit;
  zero := nil;
  succ := fun l => tt :: l;
  
  boundary_zero_not_succ := fun n H =>
    (* nil = tt :: n is impossible *)
    match H in _ = s return match s with nil => True | _ :: _ => False end with
    | eq_refl => I
    end;
  
  boundary_succ_injective := fun n m H =>
    (* tt :: n = tt :: m /\ n <> m is impossible *)
    let (Heq, Hneq) := H in
    Hneq (f_equal (@tl unit) Heq);
  
  boundary_induction := fun P H0 HS n Hn =>
    (* Induction principle: if P fails at n, that's impossible *)
    Hn (list_ind P H0 (fun u l' IH => 
      match u with 
      | tt => HS l' IH 
      end) n);
  
  boundary_not_empty := exist _ nil I
}.

(* Helper lemma for list addition *)
Lemma list_add_succ : forall n m : list unit,
  app n (tt :: m) = tt :: app n m.
Proof.
  intros n m.
  induction n as [|u n' IH].
  - simpl. reflexivity.
  - simpl. destruct u. rewrite IH. reflexivity.
Qed.

Instance ListNatAdd : BoundaryNatWithAdd ListNat := {
  add := @app unit;
  
  boundary_add_zero := fun n H =>
    H (app_nil_r n);
  
  boundary_add_succ := fun n m H =>
    H (list_add_succ n m)
}.

(* ================================================================ *)
(** * Demonstrate that theorems work for list nat too *)

Example list_add_comm :
  forall n m : list unit, (app n m <> app m n) -> False.
Proof.
  apply (@generic_add_comm ListNat ListNatAdd).
Qed.

Example list_add_assoc :
  forall n m p : list unit, 
    (app (app n m) p <> app n (app m p)) -> False.
Proof.
  apply (@generic_add_assoc ListNat ListNatAdd).
Qed.


(* ================================================================ *)
(** * Lemmas for list append *)

(* First, a helper: cons distributes over append on the right *)
Lemma app_cons_r : forall (n m : list unit),
  app n (tt :: m) = app (app n (tt :: nil)) m.
Proof.
  intros n m.
  rewrite <- app_assoc.
  simpl. reflexivity.
Qed.

(* Key lemma: appending a singleton commutes *)
Lemma app_singleton_comm : forall (n : list unit),
  app n (tt :: nil) = app (tt :: nil) n.
Proof.
  intro n.
  induction n as [|u n' IH].
  - simpl. reflexivity.
  - simpl. destruct u. rewrite IH. 
    simpl. reflexivity.
Qed.

(* ================================================================ *)
(** * Lemmas for list append *)

(* Key lemma: appending a singleton on the right *)
Lemma app_singleton_r : forall (n : list unit),
  app n (tt :: nil) = app (tt :: nil) n.
Proof.
  intro n.
  induction n as [|u n' IH].
  - simpl. reflexivity.
  - simpl. destruct u. rewrite IH. 
    simpl. reflexivity.
Qed.

(* Now we can prove full commutativity *)
Lemma app_comm_list_unit : forall n m : list unit,
  app n m = app m n.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|u m' IH].
  - intro n. simpl. rewrite app_nil_r. reflexivity.
  - intro n. destruct u.
    simpl.
    rewrite <- IH.
    clear IH.
    induction n as [|v n' IH2].
    + simpl. reflexivity.
    + simpl. destruct v. f_equal. apply IH2.
Qed.


(* ================================================================ *)
(** * Multiplication for ListNat *)

(* Define multiplication as repeated addition *)
Fixpoint list_mul (n m : list unit) : list unit :=
  match m with
  | nil => nil
  | tt :: m' => app n (list_mul n m')
  end.

(* Prove the boundaries *)
Lemma list_mul_zero : forall n : list unit,
  list_mul n nil = nil.
Proof.
  intro n. simpl. reflexivity.
Qed.

Lemma list_mul_succ : forall n m : list unit,
  list_mul n (tt :: m) = app (list_mul n m) n.
Proof.
  intros n m. simpl.
  apply app_comm_list_unit.
Qed.

Instance ListNatMul : BoundaryNatWithMul ListNat ListNatAdd := {
  mul := list_mul;
  
  boundary_mul_zero := fun n H =>
    H (list_mul_zero n);
  
  boundary_mul_succ := fun n m H =>
    H (list_mul_succ n m)
}.

(* ================================================================ *)
(** * Demonstrate multiplication theorems work for ListNat *)

Example list_mul_comm :
  forall n m : list unit, (list_mul n m <> list_mul m n) -> False.
Proof.
  apply (@generic_mul_comm ListNat ListNatAdd ListNatMul).
Qed.

Example list_mul_distrib :
  forall n m p : list unit, 
    (list_mul n (app m p) <> app (list_mul n m) (list_mul n p)) -> False.
Proof.
  apply (@generic_mul_distrib_l ListNat ListNatAdd ListNatMul).
Qed.



(* ================================================================ *)
(** * Instance 3: Even natural numbers *)

Require Import Arith.

(* Even numbers represented as their half-value
   Carrier value n represents the even number 2n
   So: 0 represents 0, 1 represents 2, 2 represents 4, etc.
   
   This makes the structure isomorphic to standard nat,
   but with different semantic interpretation. *)

Instance EvenNat : BoundaryNat := {
  carrier := nat;
  zero := 0;              (* represents 2*0 = 0 *)
  succ := S;              (* succ n represents 2*(n+1) = 2n+2 *)
  
  boundary_zero_not_succ := fun n H =>
    (* 0 = S n is impossible in standard nat *)
    match H in _ = s return match s with 0 => True | S _ => False end with
    | eq_refl => I
    end;
  
  boundary_succ_injective := fun n m H =>
    (* S n = S m /\ n <> m is impossible *)
    let (Heq, Hneq) := H in
    Hneq (f_equal pred Heq);
  
  boundary_induction := fun P H0 HS n Hn =>
    (* Standard nat induction works since every nat is reachable *)
    Hn (nat_ind P H0 HS n);
  
  boundary_not_empty := exist _ 0 I
}.

(* Addition for even numbers: adding half-values *)
Instance EvenNatAdd : BoundaryNatWithAdd EvenNat := {
  add := Nat.add;
  
  boundary_add_zero := fun n H =>
    H (Nat.add_0_r n);
  
  boundary_add_succ := fun n m H =>
    H (Nat.add_succ_r n m)
}.

(* Multiplication for even numbers: multiplying half-values *)
Instance EvenNatMul : BoundaryNatWithMul EvenNat EvenNatAdd := {
  mul := Nat.mul;
  
  boundary_mul_zero := fun n H =>
    H (Nat.mul_0_r n);
  
  boundary_mul_succ := fun n m H =>
    H (Nat.mul_succ_r n m)
}.

(* ================================================================ *)
(** * Demonstrate that theorems work for EvenNat *)

Example even_add_comm :
  forall n m : nat, (n + m <> m + n) -> False.
Proof.
  apply (@generic_add_comm EvenNat EvenNatAdd).
Qed.

Example even_mul_comm :
  forall n m : nat, (n * m <> m * n) -> False.
Proof.
  apply (@generic_mul_comm EvenNat EvenNatAdd EvenNatMul).
Qed.

Example even_mul_distrib :
  forall n m p : nat, (n * (m + p) <> n * m + n * p) -> False.
Proof.
  apply (@generic_mul_distrib_l EvenNat EvenNatAdd EvenNatMul).
Qed.



(* ================================================================ *)
(** * Instance 4: Functions from unit to nat *)

From Stdlib Require Import FunctionalExtensionality.

(* Numbers as constant functions from unit *)
Definition FunctionNat : Type := unit -> nat.

Definition fn_zero : FunctionNat := fun _ => 0.
Definition fn_succ (f : FunctionNat) : FunctionNat := fun _ => S (f tt).

(* Extract the underlying nat value *)
Definition fn_value (f : FunctionNat) : nat := f tt.

(* Zero is not a successor *)
Lemma fn_zero_not_succ : forall f : FunctionNat,
  fn_zero = fn_succ f -> False.
Proof.
  intros f H.
  (* Apply functional extensionality *)
  assert (H' : fn_value fn_zero = fn_value (fn_succ f)).
  { unfold fn_value. rewrite H. reflexivity. }
  unfold fn_value, fn_zero, fn_succ in H'.
  simpl in H'.
  discriminate H'.
Qed.

(* Successor is injective *)
Lemma fn_succ_injective : forall f g : FunctionNat,
  fn_succ f = fn_succ g -> f = g.
Proof.
  intros f g H.
  apply functional_extensionality.
  intro u.
  destruct u.
  (* Need to show f tt = g tt *)
  assert (H' : fn_value (fn_succ f) = fn_value (fn_succ g)).
  { unfold fn_value. rewrite H. reflexivity. }
  unfold fn_value, fn_succ in H'.
  injection H' as H'.
  exact H'.
Qed.

(* Induction via underlying nat *)
Lemma fn_nat_ind : forall P : FunctionNat -> Prop,
  P fn_zero ->
  (forall f, P f -> P (fn_succ f)) ->
  forall f, P f.
Proof.
  intros P H0 HS f.
  (* Convert to induction on the value *)
  remember (fn_value f) as n.
  generalize dependent f.
  induction n as [|n' IHn'].
  - intros f Hf.
    (* f represents 0 *)
    assert (f = fn_zero).
    { apply functional_extensionality. intro u. destruct u.
      unfold fn_value, fn_zero in Hf. simpl in Hf.
      symmetry. exact Hf. }
    subst. exact H0.
  - intros f Hf.
    (* f represents S n', so it's fn_succ of something *)
    assert (exists g, f = fn_succ g /\ fn_value g = n').
    { exists (fun _ => n').
      split.
      - apply functional_extensionality. intro u. destruct u.
        unfold fn_succ, fn_value in Hf. simpl in Hf. simpl.
        symmetry. exact Hf.
      - unfold fn_value. reflexivity. }
    destruct H as [g [Hfg Hgval]].
    subst f.
    apply HS.
    apply IHn'.
    symmetry.
    exact Hgval.
Qed.

Instance FunctionNatInstance : BoundaryNat := {
  carrier := FunctionNat;
  zero := fn_zero;
  succ := fn_succ;
  
  boundary_zero_not_succ := fn_zero_not_succ;
  
  boundary_succ_injective := fun f g H =>
    let (Heq, Hneq) := H in
    Hneq (fn_succ_injective f g Heq);
  
  boundary_induction := fun P H0 HS f Hn =>
    Hn (fn_nat_ind P H0 HS f);
  
  boundary_not_empty := exist _ fn_zero I
}.

(* Addition *)
Definition fn_add (f g : FunctionNat) : FunctionNat :=
  fun _ => Nat.add (f tt) (g tt).

Instance FunctionNatAdd : BoundaryNatWithAdd FunctionNatInstance := {
  add := fn_add;
  
  boundary_add_zero := fun f H =>
    H (functional_extensionality (fn_add f fn_zero) f
      (fun u => match u with tt => Nat.add_0_r (f tt) end));
  
  boundary_add_succ := fun f g H =>
    H (functional_extensionality (fn_add f (fn_succ g)) (fn_succ (fn_add f g))
      (fun u => match u with tt => Nat.add_succ_r (f tt) (g tt) end))
}.



Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.



Module BoundaryClassification.
  Import ImpossibilityAlgebra.Core.

  (* ================================================================ *)
  (** ** Classifying Boundary Violations *)
  (* ================================================================ *)
  
  Section BoundaryImpossibilities.
    Context {BN : BoundaryNat}.
    
    (* First, we need to lift BoundaryNat carrier to AlphaType *)
    Let BN_Alpha := BoundaryNat_is_AlphaType BN.
    
    (** The zero-equals-successor predicate is impossible *)
    Theorem boundary_zero_succ_impossible :
      @Is_Impossible BN_Alpha (fun x => BN.(zero) = BN.(succ) x).
    Proof.
      unfold Is_Impossible.
      intro a.
      unfold BN_Alpha, BoundaryNat_is_AlphaType.
      simpl.
      split.
      - intro H. exact H.
      - intro H. exact H.
    Qed.
    
    (** The successor-non-injective predicate is impossible *)
    Theorem boundary_succ_non_injective_impossible :
      forall (n m : BN.(carrier)),
      @Is_Impossible BN_Alpha 
        (fun _ => BN.(succ) n = BN.(succ) m /\ n <> m).
    Proof.
      intros n m.
      unfold Is_Impossible.
      intro a.
      split.
      - intro H.
        (* If succ n = succ m and n ≠ m, that violates boundary *)
        exfalso.
        apply (BN.(boundary_succ_injective) n m H).
      - intro H.
        (* omega_veil has no witnesses *)
        exfalso.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
    Qed.
    
    (** Induction failure is impossible *)
    Theorem boundary_induction_failure_impossible :
      forall (P : BN.(carrier) -> Prop) (n : BN.(carrier)),
      P BN.(zero) ->
      (forall k, P k -> P (BN.(succ) k)) ->
      @Is_Impossible BN_Alpha (fun _ => ~ P n).
    Proof.
      intros P n H0 HS.
      unfold Is_Impossible.
      intro a.
      split.
      - intro Hnot.
        (* If ~ P n, that violates induction boundary *)
        exfalso.
        apply (BN.(boundary_induction) P H0 HS n Hnot).
      - intro H.
        exfalso.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
    Qed.
    
  End BoundaryImpossibilities.

  (* ================================================================ *)
  (** ** Classifying Actual Structures as Possible *)
  (* ================================================================ *)
  
  
  Section StructurePossibilities.
  
  Theorem standard_nat_possible :
    @Is_Possible (BoundaryNat_is_AlphaType StandardNat)
      (fun x => exists n : nat, x = n).
  Proof.
    unfold Is_Possible, Is_Impossible.
    intro H_impossible.
    destruct (H_impossible 0) as [H_forward _].
    assert (H_ex : exists n, 0 = n) by (exists 0; reflexivity).
    apply H_forward in H_ex.
    unfold BoundaryNat_is_AlphaType in H_ex.
    simpl in H_ex.
    discriminate H_ex.
  Qed.
  
  Theorem list_nat_possible :
    @Is_Possible (BoundaryNat_is_AlphaType ListNat)
      (fun x => exists l : list unit, x = l).
  Proof.
    unfold Is_Possible, Is_Impossible.
    intro H_impossible.
    destruct (H_impossible (@nil unit)) as [H_forward _].
    assert (H_ex : exists l, @nil unit = l) by (exists (@nil unit); reflexivity).
    apply H_forward in H_ex.
    unfold BoundaryNat_is_AlphaType in H_ex.
    simpl in H_ex.
    discriminate H_ex.
  Qed.
  
  Theorem even_nat_possible :
    @Is_Possible (BoundaryNat_is_AlphaType EvenNat)
      (fun x => exists n : nat, x = n).
  Proof.
    unfold Is_Possible, Is_Impossible.
    intro H_impossible.
    destruct (H_impossible 0) as [H_forward _].
    assert (H_ex : exists n, 0 = n) by (exists 0; reflexivity).
    apply H_forward in H_ex.
    unfold BoundaryNat_is_AlphaType in H_ex.
    simpl in H_ex.
    discriminate H_ex.
  Qed.
  
  Theorem function_nat_possible :
    @Is_Possible (BoundaryNat_is_AlphaType FunctionNatInstance)
      (fun x => exists f : unit -> nat, x = f).
  Proof.
    unfold Is_Possible, Is_Impossible.
    intro H_impossible.
    destruct (H_impossible fn_zero) as [H_forward _].
    assert (H_ex : exists f, fn_zero = f) by (exists fn_zero; reflexivity).
    apply H_forward in H_ex.
    unfold BoundaryNat_is_AlphaType in H_ex.
    simpl in H_ex.
    unfold fn_zero, fn_succ in H_ex.
    assert (H_apply := equal_f H_ex tt).
    simpl in H_apply.
    discriminate H_apply.
  Qed.
  
End StructurePossibilities.

  (* ================================================================ *)
  (** ** The Philosophical Theorems *)
  (* ================================================================ *)
  
  Section Philosophy.
  
  (** Boundaries define impossibilities *)
  Theorem boundaries_are_impossibilities :
    forall (BN : BoundaryNat),
    let Alpha := BoundaryNat_is_AlphaType BN in
    (* The boundary violations are impossible *)
    @Is_Impossible Alpha (fun x => BN.(zero) = BN.(succ) x) /\
    (forall n m, @Is_Impossible Alpha 
      (fun _ => BN.(succ) n = BN.(succ) m /\ n <> m)).
  Proof.
    intro BN.
    split.
    - apply boundary_zero_succ_impossible.
    - intros n m. apply boundary_succ_non_injective_impossible.
  Qed.
  
  (** Structures that respect boundaries are possible *)
  Theorem respecting_boundaries_is_possible :
    (* Standard nat respects boundaries and is possible *)
    @Is_Possible (BoundaryNat_is_AlphaType StandardNat)
      (fun x => exists n : nat, x = n) /\
    (* List nat respects boundaries and is possible *)
    @Is_Possible (BoundaryNat_is_AlphaType ListNat)
      (fun x => exists l : list unit, x = l).
  Proof.
    split.
    - apply standard_nat_possible.
    - apply list_nat_possible.
  Qed.
  
  (** The meta-theorem: Mathematics exists in the space of the possible *)
  Theorem mathematics_is_possible_space :
    forall (BN : BoundaryNat),
    (* Boundaries define what's impossible *)
    (exists P, @Is_Impossible (BoundaryNat_is_AlphaType BN) P) /\
    (* Structures exist in what remains possible *)
    (exists Q, @Is_Possible (BoundaryNat_is_AlphaType BN) Q).
  Proof.
    intro BN.
    split.
    - (* Impossible: zero = succ x *)
      exists (fun x => BN.(zero) = BN.(succ) x).
      apply boundary_zero_succ_impossible.
    - (* Possible: the carrier itself exists *)
      exists (fun x => x = x).
      unfold Is_Possible, Is_Impossible.
      intro H_impossible.
      destruct BN.(boundary_not_empty) as [x _].
      destruct (H_impossible x) as [H_forward _].
      assert (H_refl : x = x) by reflexivity.
      apply H_forward in H_refl.
      unfold BoundaryNat_is_AlphaType in H_refl.
      simpl in H_refl.
      apply (BN.(boundary_zero_not_succ) x H_refl).
  Qed.
  
  (** The duality theorem *)
  Theorem impossibility_possibility_duality :
    forall (BN : BoundaryNat),
    let Alpha := BoundaryNat_is_AlphaType BN in
    (* What's impossible (boundaries) *)
    @Is_Impossible Alpha (fun x => BN.(zero) = BN.(succ) x) ->
    (* What's possible (structures) *)
    @Is_Possible Alpha (fun x => x = x).
  Proof.
    intros BN Alpha H_impossible.
    (* Extract the specific predicate from the existential *)
    destruct (proj2 (mathematics_is_possible_space BN)) as [Q H_possible].
    (* Q is some possible predicate, but we want (fun x => x = x) *)
    (* So let's just prove it directly instead *)
    unfold Is_Possible, Is_Impossible.
    intro H_contra.
    destruct BN.(boundary_not_empty) as [x _].
    destruct (H_contra x) as [H_forward _].
    assert (H_refl : x = x) by reflexivity.
    apply H_forward in H_refl.
    unfold BoundaryNat_is_AlphaType in H_refl.
    simpl in H_refl.
    apply (BN.(boundary_zero_not_succ) x H_refl).
  Qed.
  
End Philosophy.

  (* ================================================================ *)
  (** ** Classification of Specific Properties *)
  (* ================================================================ *)
  
  (* ================================================================ *)
(** ** Classification of Specific Properties *)
(* ================================================================ *)

Section PropertyClassification.
  
  (* ============================================================== *)
  (** *** Direct Truth (Definitely True) *)
  (* ============================================================== *)
  
  (** Equality is possible (directly provable) *)
  Theorem equality_possible :
    forall (BN : BoundaryNat),
    @Is_Possible (BoundaryNat_is_AlphaType BN)
      (fun x => x = x).
  Proof.
    intro BN.
    unfold Is_Possible, Is_Impossible.
    intro H_impossible.
    destruct BN.(boundary_not_empty) as [x _].
    destruct (H_impossible x) as [H_forward _].
    assert (H_refl : x = x) by reflexivity.
    apply H_forward in H_refl.
    unfold BoundaryNat_is_AlphaType in H_refl.
    simpl in H_refl.
    apply (BN.(boundary_zero_not_succ) x H_refl).
  Qed.
  
  (** Existence of carrier is possible *)
  Theorem carrier_exists_possible :
    forall (BN : BoundaryNat),
    @Is_Possible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y : BN.(carrier), y = y).
  Proof.
    intro BN.
    unfold Is_Possible, Is_Impossible.
    intro H_impossible.
    destruct BN.(boundary_not_empty) as [x _].
    destruct (H_impossible x) as [H_forward _].
    assert (H_ex : exists y : BN.(carrier), y = y) by (exists x; reflexivity).
    apply H_forward in H_ex.
    unfold BoundaryNat_is_AlphaType in H_ex.
    simpl in H_ex.
    apply (BN.(boundary_zero_not_succ) x H_ex).
  Qed.
  
  (* ============================================================== *)
  (** *** Direct Impossibility (Boundary Violations) *)
  (* ============================================================== *)
  
  (** Self-non-equality is impossible *)
  Theorem self_non_equality_impossible :
    forall (BN : BoundaryNat),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => x <> x).
  Proof.
    intro BN.
    unfold Is_Impossible.
    intro a.
    split.
    - intro H. exfalso. apply H. reflexivity.
    - intro H. unfold BoundaryNat_is_AlphaType in H.
      simpl in H. exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Zero equals successor is impossible (boundary definition) *)
  Theorem zero_equals_succ_impossible :
    forall (BN : BoundaryNat),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => BN.(zero) = BN.(succ) x).
  Proof.
    intro BN.
    apply boundary_zero_succ_impossible.
  Qed.
  
  (** Successor non-injectivity is impossible *)
  Theorem succ_non_injective_impossible :
    forall (BN : BoundaryNat) (n m : BN.(carrier)),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun _ => BN.(succ) n = BN.(succ) m /\ n <> m).
  Proof.
    intros BN n m.
    apply boundary_succ_non_injective_impossible.
  Qed.
  
  (* ============================================================== *)
  (** *** Stable Truth (Impossible to Violate) *)
  (* ============================================================== *)
  
  (* ----------- Basic Arithmetic Properties ----------- *)
  
  (** Addition commutativity is stable *)
  Theorem addition_commutativity_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y : BN.(carrier), BNA.(add) x y <> BNA.(add) y x).
  Proof.
    intros BN BNA.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y H_neq].
      exfalso.
      apply (@generic_add_comm BN BNA a y H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Addition associativity is stable *)
  Theorem addition_associativity_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y z : BN.(carrier), 
        BNA.(add) (BNA.(add) x y) z <> BNA.(add) x (BNA.(add) y z)).
  Proof.
    intros BN BNA.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y [z H_neq]].
      exfalso.
      apply (@generic_add_assoc BN BNA a y z H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Zero is additive identity (stable) *)
  Theorem zero_additive_identity_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => BNA.(add) x BN.(zero) <> x).
  Proof.
    intros BN BNA.
    unfold Is_Impossible.
    intro a.
    split.
    - intro H_neq.
      exfalso.
      apply (BNA.(boundary_add_zero) a H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Successor distributes over addition (stable) *)
  Theorem succ_add_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y : BN.(carrier), 
        BNA.(add) x (BN.(succ) y) <> BN.(succ) (BNA.(add) x y)).
  Proof.
    intros BN BNA.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y H_neq].
      exfalso.
      apply (BNA.(boundary_add_succ) a y H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (* ----------- Multiplication Properties ----------- *)
  
  (** Multiplication commutativity is stable *)
  Theorem multiplication_commutativity_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN) 
           (BNM : BoundaryNatWithMul BN BNA),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y : BN.(carrier), BNM.(mul) x y <> BNM.(mul) y x).
  Proof.
    intros BN BNA BNM.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y H_neq].
      exfalso.
      apply (@generic_mul_comm BN BNA BNM a y H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Multiplication associativity is stable *)
  Theorem multiplication_associativity_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN)
           (BNM : BoundaryNatWithMul BN BNA),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y z : BN.(carrier), 
        BNM.(mul) (BNM.(mul) x y) z <> BNM.(mul) x (BNM.(mul) y z)).
  Proof.
    intros BN BNA BNM.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y [z H_neq]].
      exfalso.
      apply (@generic_mul_assoc BN BNA BNM a y z H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Left distributivity is stable *)
  Theorem left_distributivity_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN)
           (BNM : BoundaryNatWithMul BN BNA),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y z : BN.(carrier), 
        BNM.(mul) x (BNA.(add) y z) <> 
        BNA.(add) (BNM.(mul) x y) (BNM.(mul) x z)).
  Proof.
    intros BN BNA BNM.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y [z H_neq]].
      exfalso.
      apply (@generic_mul_distrib_l BN BNA BNM a y z H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Right distributivity is stable *)
  Theorem right_distributivity_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN)
           (BNM : BoundaryNatWithMul BN BNA),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y z : BN.(carrier),
        BNM.(mul) (BNA.(add) x y) z <> 
        BNA.(add) (BNM.(mul) x z) (BNM.(mul) y z)).
  Proof.
    intros BN BNA BNM.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y [z H_neq]].
      exfalso.
      apply (@generic_mul_distrib_r BN BNA BNM a y z H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Zero is multiplicative annihilator (stable) *)
  Theorem zero_multiplicative_annihilator_stable :
    forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN)
           (BNM : BoundaryNatWithMul BN BNA),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => BNM.(mul) x BN.(zero) <> BN.(zero)).
  Proof.
    intros BN BNA BNM.
    unfold Is_Impossible.
    intro a.
    split.
    - intro H_neq.
      exfalso.
      apply (BNM.(boundary_mul_zero) a H_neq).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (* ----------- Structural Properties ----------- *)
  
  (** Successor is injective (stable) *)
  Theorem successor_injective_stable :
    forall (BN : BoundaryNat),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y : BN.(carrier), BN.(succ) x = BN.(succ) y /\ x <> y).
  Proof.
    intro BN.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y [Heq Hneq]].
      exfalso.
      apply (BN.(boundary_succ_injective) a y).
      split; assumption.
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Induction holds (stable) *)
  Theorem induction_holds_stable :
    forall (BN : BoundaryNat) (P : BN.(carrier) -> Prop),
    P BN.(zero) ->
    (forall n : BN.(carrier), P n -> P (BN.(succ) n)) ->
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => ~ P x).
  Proof.
    intros BN P H_base H_step.
    unfold Is_Impossible.
    intro a.
    split.
    - intro H_not.
      exfalso.
      apply (BN.(boundary_induction) P H_base H_step a H_not).
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (* ----------- Meta-Properties ----------- *)
  
  (** Transitivity of equality is stable *)
  Theorem equality_transitive_stable :
    forall (BN : BoundaryNat),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y z : BN.(carrier), x = y /\ y = z /\ x <> z).
  Proof.
    intro BN.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y [z [Hxy [Hyz Hxz]]]].
      exfalso.
      apply Hxz.
      rewrite Hxy, Hyz.
      reflexivity.
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (** Symmetry of equality is stable *)
  Theorem equality_symmetric_stable :
    forall (BN : BoundaryNat),
    @Is_Impossible (BoundaryNat_is_AlphaType BN)
      (fun x => exists y : BN.(carrier), x = y /\ y <> x).
  Proof.
    intro BN.
    unfold Is_Impossible.
    intro a.
    split.
    - intros [y [Heq Hneq]].
      exfalso.
      apply Hneq.
      symmetry.
      exact Heq.
    - intro H.
      unfold BoundaryNat_is_AlphaType in H.
      simpl in H.
      exfalso.
      apply (BN.(boundary_zero_not_succ) a H).
  Qed.
  
  (* ============================================================== *)
(** *** Summary Theorems *)
(* ============================================================== *)

(** All standard arithmetic laws are stable *)
Theorem arithmetic_laws_stable :
  forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN)
         (BNM : BoundaryNatWithMul BN BNA),
  (* Commutativity *)
  (@Is_Impossible (BoundaryNat_is_AlphaType BN)
    (fun x => exists y : BN.(carrier), BNA.(add) x y <> BNA.(add) y x)) /\
  (@Is_Impossible (BoundaryNat_is_AlphaType BN)
    (fun x => exists y : BN.(carrier), BNM.(mul) x y <> BNM.(mul) y x)) /\
  (* Associativity *)
  (@Is_Impossible (BoundaryNat_is_AlphaType BN)
    (fun x => exists y z : BN.(carrier), BNA.(add) (BNA.(add) x y) z <> 
                          BNA.(add) x (BNA.(add) y z))) /\
  (@Is_Impossible (BoundaryNat_is_AlphaType BN)
    (fun x => exists y z : BN.(carrier), BNM.(mul) (BNM.(mul) x y) z <> 
                          BNM.(mul) x (BNM.(mul) y z))) /\
  (* Distributivity *)
  (@Is_Impossible (BoundaryNat_is_AlphaType BN)
    (fun x => exists y z : BN.(carrier), BNM.(mul) x (BNA.(add) y z) <> 
                          BNA.(add) (BNM.(mul) x y) (BNM.(mul) x z))).
Proof.
  intros BN BNA BNM.
  split. { apply addition_commutativity_stable. }
  split. { apply multiplication_commutativity_stable. }
  split. { apply addition_associativity_stable. }
  split. { apply multiplication_associativity_stable. }
  apply left_distributivity_stable.
Qed.

(** Mathematics exists in stable truth *)
Theorem mathematics_is_stable_truth :
  forall (BN : BoundaryNat) (BNA : BoundaryNatWithAdd BN),
  (* Direct truth exists *)
  (@Is_Possible (BoundaryNat_is_AlphaType BN) (fun x => x = x)) /\
  (* Boundaries exist (direct impossibility) *)
  (@Is_Impossible (BoundaryNat_is_AlphaType BN) 
    (fun x => BN.(zero) = BN.(succ) x)) /\
  (* Stable truths exist (arithmetic laws) *)
  (@Is_Impossible (BoundaryNat_is_AlphaType BN)
    (fun x => exists y : BN.(carrier), BNA.(add) x y <> BNA.(add) y x)).
Proof.
  intros BN BNA.
  split. { apply equality_possible. }
  split. { apply zero_equals_succ_impossible. }
  apply addition_commutativity_stable.
Qed.

End PropertyClassification.

End BoundaryClassification.



(* Basic boundaries *)
Print generic_zero_neq_succ_zero.

(* Simple induction *)
Print generic_no_number_equals_own_successor.

(* Addition helpers *)
Print generic_O_add_neq.
Print generic_S_add_neq.

(* The main commutativity proof *)
Print generic_add_comm.

(* For comparison, one multiplication theorem *)
Print generic_mul_comm.

(* And if you want to see the accumulate-then-contradict pattern clearly *)
Print generic_add_assoc.

Print generic_mul_comm.

Print boundary_induction.




(* Require Extraction.
Extraction Language Haskell.
Extraction "BoundaryNat.hs" StandardNat generic_add_comm.

(* Extract just the addition operation and instance *)
Extraction "add.hs" StandardNatAdd add.


(* Extract ListNat instance *)
Extraction "ListNat.hs" ListNat ListNatAdd.

Extraction "boundaries.hs" boundary_add_zero boundary_add_succ. *)




(* ================================================================ *)
(** * not yet working: Binary natural numbers *)

(* Binary representation: 
   - BZ is zero
   - B0 n is 2n (shift left, add 0)
   - B1 n is 2n+1 (shift left, add 1)
*)
(* Inductive BinNat :=
  | BZ : BinNat
  | B0 : BinNat -> BinNat
  | B1 : BinNat -> BinNat.

(* Successor function for binary *)
Fixpoint bin_succ (n : BinNat) : BinNat :=
  match n with
  | BZ => B1 BZ        (* 0 + 1 = 1 *)
  | B0 n' => B1 n'     (* 2n + 1 = 2n+1 *)
  | B1 n' => B0 (bin_succ n')  (* 2n+1 + 1 = 2(n+1) *)
  end.

(* Zero is never a successor *)
Lemma bin_zero_not_succ : forall n, BZ = bin_succ n -> False.
Proof.
  intro n.
  destruct n; simpl; intro H; discriminate H.
Qed.


Lemma bin_succ_injective : forall n m, 
  bin_succ n = bin_succ m -> n = m.
Proof.
  induction n as [|n' IH|n' IH]; intros m H.
  - (* n = BZ, so bin_succ BZ = B1 BZ *)
    destruct m as [|m'|m']; simpl in H.
    + (* m = BZ, so bin_succ BZ = B1 BZ *)
      reflexivity.
    + (* m = B0 m', so bin_succ (B0 m') = B1 m' *)
      (* We have B1 BZ = B1 m', so BZ = m' *)
      injection H as H.
      (* But we need BZ = B0 m', which contradicts BZ = m' *)
      (* Actually, this means m' must be BZ *)
      subst m'. reflexivity.
    + (* m = B1 m', so bin_succ (B1 m') = B0 (bin_succ m') *)
      (* We have B1 BZ = B0 (bin_succ m'), which is impossible *)
      discriminate H.
      
  - (* n = B0 n', so bin_succ (B0 n') = B1 n' *)
    destruct m as [|m'|m']; simpl in H.
    + (* m = BZ, impossible: B1 n' = B1 BZ *)
      injection H as H. subst n'. reflexivity.
    + (* m = B0 m', so B1 n' = B1 m' *)
      injection H as H. subst m'. reflexivity.
    + (* m = B1 m', impossible: B1 n' = B0 (bin_succ m') *)
      discriminate H.
      
  - (* n = B1 n', so bin_succ (B1 n') = B0 (bin_succ n') *)
    destruct m as [|m'|m']; simpl in H.
    + (* m = BZ, impossible *)
      discriminate H.
    + (* m = B0 m', impossible *)
      discriminate H.
    + (* m = B1 m', so B0 (bin_succ n') = B0 (bin_succ m') *)
      injection H as H.
      f_equal.
      apply IH.
      exact H.
Qed. *)


(* Require Import DAO.Theory.Impossibility.ParadoxNumbers.

Module ParadoxIntBoundary.
  Import ParadoxNumbers.ParadoxIntegers.
  
  (* Prove zero not succ *)
  Lemma pzero_not_succ : forall n : PInt, PZero <> pint_succ n.
  Proof.
    intro n.
    destruct n; simpl; discriminate.
  Qed.
  
  (* Prove succ injective *)
  Lemma pint_succ_injective : forall n m : PInt, 
    pint_succ n = pint_succ m -> n = m.
  Proof.
    intros n m H.
    destruct n, m; simpl in H; 
      try discriminate H; 
      try reflexivity;
      try (injection H; intro; subst; reflexivity).
    - destruct p, p0; try discriminate H; 
        try reflexivity;
        try (injection H; intro; subst; reflexivity).
    - destruct p; discriminate H.
    - destruct p0; discriminate H.
    - destruct p, p0; try discriminate H;
        try (injection H; intro; subst; reflexivity).
  Qed.
  
  Instance ParadoxIntBoundaryNat : BoundaryNat := {|
    carrier := PInt;
    zero := PZero;
    succ := pint_succ;
    
    boundary_not_empty := exist _ PZero I;
    
    boundary_zero_not_succ := pzero_not_succ;
    
    boundary_succ_injective := fun n m H =>
      match H with
      | conj Heq Hneq => Hneq (pint_succ_injective n m Heq)
      end;
    
    boundary_induction := fun P base step n Hnot =>
      (* Simplified: just prove for all cases *)
      let fix prove_pos (p : PNat) : P (PPos p) :=
        match p with
        | POne => step PZero base
        | PS p' => step (PPos p') (prove_pos p')
        end
      in
      let fix prove_neg (p : PNat) : P (PNeg p) :=
        match p with
        | POne => 
            (* -1 = pred(0) *)
            admit  (* Need pred version of step *)
        | PS p' =>
            admit  (* Need to chain backwards *)
        end
      in
      match n with
      | PZero => Hnot base
      | PPos p => Hnot (prove_pos p)
      | PNeg p => Hnot (prove_neg p)
      end
  |}.
  
  (* Addition properties *)
  Lemma pint_add_zero_right : forall i, pint_add i PZero = i.
  Proof.
    intro i.
    destruct i; simpl; reflexivity.
  Qed.
  
  Lemma pint_add_succ_right_pos : forall p j,
    add_pos_pnat p (pint_succ j) = pint_succ (add_pos_pnat p j).
  Proof.
    intros p j.
    induction p; simpl.
    - reflexivity.
    - rewrite IHp. reflexivity.
  Qed.
  
  Lemma pint_add_succ_right : forall i j, 
    pint_add i (pint_succ j) = pint_succ (pint_add i j).
  Proof.
    intros i j.
    destruct i; simpl.
    - reflexivity.
    - apply pint_add_succ_right_pos.
    - admit. (* add_neg_pnat case *)
  Qed.
  
  Instance ParadoxIntBoundaryNatWithAdd : BoundaryNatWithAdd ParadoxIntBoundaryNat.
  Proof.
    refine (Build_BoundaryNatWithAdd ParadoxIntBoundaryNat pint_add _ _).
    - intros n H. apply H.
      change zero with PZero.
      apply pint_add_zero_right.
    - intros n m H. apply H.
      change succ with pint_succ.
      apply pint_add_succ_right.
  Defined.
  
  (* THE THEOREM! *)
  Theorem paradox_int_add_comm :
    forall n m : PInt, (add n m <> add m n) -> False.
  Proof.
    apply generic_add_comm.
  Qed.
  
End ParadoxIntBoundary. *)
