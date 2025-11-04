Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.

(* ================================================================ *)
(** * BoundaryNat: The Interface *)

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
  
  (* Non-emptiness - changed from exists to sig *)
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
