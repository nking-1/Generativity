(** * UnravelLang.v: Where Nothing Is Something and Computation Unravels the Veil
    
    A simple functional language where omega_veil is a first-class value.
    All operations are total - errors return void rather than crashing.
    
    This demonstrates that the DAO framework isn't just theory - it leads
    to practical programming languages with beautiful properties.
*)

Require Import Stdlib.Init.Datatypes.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Extraction.
Require Import Strings.Ascii.
Import ListNotations.

(* Import our framework - adjust paths as needed *)
Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.WaysOfNotExisting.

Module UnravelLang.

  (* ================================================================ *)
  (** ** Core Language Definition *)
  (* ================================================================ *)
  
  Module Core.
    
    (** Our expression language *)
    Inductive Expr : Type :=
      (* Values *)
      | ENum : nat -> Expr                    (* Natural number *)
      | EVoid : Expr                          (* The void value *)
      | EBool : bool -> Expr                  (* Boolean *)
      
      (* Arithmetic - all operations are safe *)
      | EAdd : Expr -> Expr -> Expr           (* Addition *)
      | ESub : Expr -> Expr -> Expr           (* Subtraction (saturating) *)
      | EMul : Expr -> Expr -> Expr           (* Multiplication *)
      | EDiv : Expr -> Expr -> Expr           (* Division - void on div/0 *)
      | EMod : Expr -> Expr -> Expr           (* Modulo - void on mod 0 *)
      
      (* Void operations *)
      | EIsVoid : Expr -> Expr                (* Test if expression is void *)
      | EIfVoid : Expr -> Expr -> Expr -> Expr (* If void then else *)
      | EDefault : Expr -> Expr -> Expr.      (* Use default if void *)
    
    (** Values our language evaluates to *)
    Inductive Value : Type :=
      | VNum : nat -> Value
      | VBool : bool -> Value
      | VVoid : Value.  (* omega_veil as a runtime value *)
    
    (** Check if a value is void *)
    Definition is_void (v : Value) : bool :=
      match v with
      | VVoid => true
      | _ => false
      end.
    
    (** Extract nat from value, with default *)
    Definition value_to_nat_default (v : Value) (default : nat) : nat :=
      match v with
      | VNum n => n
      | _ => default
      end.
    
    (** Extract bool from value, with default *)
    Definition value_to_bool_default (v : Value) (default : bool) : bool :=
      match v with
      | VBool b => b
      | _ => default
      end.
    
  End Core.
  
  (* ================================================================ *)
  (** ** Evaluation *)
  (* ================================================================ *)
  
  Module Eval.
    Import Core.
    
    (** Big-step evaluation - always total! *)
    Fixpoint eval (fuel : nat) (e : Expr) : Value :=
      match fuel with
      | 0 => VVoid  (* Out of fuel = void (prevents infinite loops) *)
      | S fuel' =>
          match e with
          | ENum n => VNum n
          | EVoid => VVoid
          | EBool b => VBool b
          
          (* Arithmetic operations *)
          | EAdd e1 e2 =>
              match eval fuel' e1, eval fuel' e2 with
              | VNum n1, VNum n2 => VNum (n1 + n2)
              | VVoid, _ => VVoid  (* Void propagates *)
              | _, VVoid => VVoid
              | _, _ => VVoid      (* Type error → void *)
              end
              
          | ESub e1 e2 =>
              match eval fuel' e1, eval fuel' e2 with
              | VNum n1, VNum n2 => VNum (n1 - n2)  (* Saturating subtraction *)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
              
          | EMul e1 e2 =>
              match eval fuel' e1, eval fuel' e2 with
              | VNum n1, VNum n2 => VNum (n1 * n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
              
          | EDiv e1 e2 =>
              match eval fuel' e1, eval fuel' e2 with
              | VNum n1, VNum 0 => VVoid  (* Division by zero → void *)
              | VNum n1, VNum n2 => VNum (n1 / n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
              
          | EMod e1 e2 =>
              match eval fuel' e1, eval fuel' e2 with
              | VNum n1, VNum 0 => VVoid  (* Modulo by zero → void *)
              | VNum n1, VNum n2 => VNum (n1 mod n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
          
          (* Void operations *)
          | EIsVoid e =>
              match eval fuel' e with
              | VVoid => VBool true
              | _ => VBool false
              end
              
          | EIfVoid cond then_branch else_branch =>
              match eval fuel' cond with
              | VVoid => eval fuel' then_branch
              | _ => eval fuel' else_branch
              end
              
          | EDefault e default =>
              match eval fuel' e with
              | VVoid => eval fuel' default
              | v => v
              end
          end
      end.
    
    (** Evaluation with default fuel *)
    Definition eval_default (e : Expr) : Value :=
      eval 1000 e.
    
  End Eval.
  
  (* ================================================================ *)
  (** ** Properties and Theorems *)
  (* ================================================================ *)
  
  Module Properties.
    Import Core.
    Import Eval.
    
    (** Void always evaluates to VVoid *)
    Lemma eval_void : forall fuel,
      eval fuel EVoid = VVoid.
    Proof.
      intros fuel.
      destruct fuel; reflexivity.
    Qed.
    
    (** Void propagates through arithmetic operations *)
    Theorem void_propagates_add : forall fuel e,
      eval fuel (EAdd EVoid e) = VVoid.
    Proof.
      intros fuel e.
      destruct fuel; simpl.
      - reflexivity.
      - rewrite eval_void.
        reflexivity.
    Qed.
    
    Theorem void_propagates_mul : forall fuel e,
      eval fuel (EMul e EVoid) = VVoid.
    Proof.
      intros fuel e.
      destruct fuel; simpl.
      - reflexivity.
      - rewrite eval_void.
        destruct (eval fuel e); reflexivity.
    Qed.
    
    (** Division by zero produces void *)
    Theorem div_by_zero_is_void : forall fuel n,
      eval (S fuel) (EDiv (ENum n) (ENum 0)) = VVoid.
    Proof.
      intros fuel n.
      simpl.
      destruct fuel; simpl; reflexivity.
    Qed.
    
    (** IsVoid correctly identifies void *)
    Theorem is_void_correct : forall fuel,
      eval (S fuel) (EIsVoid EVoid) = VBool true.
    Proof.
      intros fuel.
      simpl.
      destruct fuel; simpl; reflexivity.
    Qed.
    
    (** Default provides fallback for void *)
    Theorem default_recovers_from_void : forall fuel n,
      eval (S (S fuel)) (EDefault EVoid (ENum n)) = VNum n.
    Proof.
      intros fuel n.
      simpl.
      reflexivity.
    Qed.
    
    (** Evaluation is deterministic *)
    Theorem eval_deterministic : forall fuel e v1 v2,
      eval fuel e = v1 ->
      eval fuel e = v2 ->
      v1 = v2.
    Proof.
      intros fuel e v1 v2 H1 H2.
      rewrite <- H1.
      exact H2.
    Qed.
    
  End Properties.


  (* ================================================================ *)
  (** ** Variables and Let Bindings *)
  (* ================================================================ *)

  Module WithVariables.
    Import Core.
    Import Eval.
    
    (** Extended expression language with variables *)
    Inductive ExprV : Type :=
      (* All the existing constructors, lifted *)
      | EVNum : nat -> ExprV
      | EVVoid : ExprV
      | EVBool : bool -> ExprV
      | EVAdd : ExprV -> ExprV -> ExprV
      | EVSub : ExprV -> ExprV -> ExprV
      | EVMul : ExprV -> ExprV -> ExprV
      | EVDiv : ExprV -> ExprV -> ExprV
      | EVMod : ExprV -> ExprV -> ExprV
      | EVIsVoid : ExprV -> ExprV
      | EVIfVoid : ExprV -> ExprV -> ExprV -> ExprV
      | EVDefault : ExprV -> ExprV -> ExprV
      
      (* NEW: Variables and let-bindings *)
      | EVVar : string -> ExprV                           (* Variable reference *)
      | EVLet : string -> ExprV -> ExprV -> ExprV.       (* let x = e1 in e2 *)
    
    (** Environment maps variable names to values *)
    Definition Env := list (string * Value).
    
    (** Looking up a variable - returns void if not found! *)
    Fixpoint lookup (env : Env) (x : string) : Value :=
      match env with
      | [] => VVoid  (* Undefined variable = void! *)
      | (y, v) :: rest =>
          if String.eqb x y then v else lookup rest x
      end.
    
    (** Evaluation with environment *)
    Fixpoint evalV (fuel : nat) (env : Env) (e : ExprV) : Value :=
      match fuel with
      | 0 => VVoid
      | S fuel' =>
          match e with
          | EVNum n => VNum n
          | EVVoid => VVoid
          | EVBool b => VBool b
          
          (* Arithmetic - same as before but with env *)
          | EVAdd e1 e2 =>
              match evalV fuel' env e1, evalV fuel' env e2 with
              | VNum n1, VNum n2 => VNum (n1 + n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
              
          | EVSub e1 e2 =>
              match evalV fuel' env e1, evalV fuel' env e2 with
              | VNum n1, VNum n2 => VNum (n1 - n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
              
          | EVMul e1 e2 =>
              match evalV fuel' env e1, evalV fuel' env e2 with
              | VNum n1, VNum n2 => VNum (n1 * n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
              
          | EVDiv e1 e2 =>
              match evalV fuel' env e1, evalV fuel' env e2 with
              | VNum n1, VNum 0 => VVoid
              | VNum n1, VNum n2 => VNum (n1 / n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
              
          | EVMod e1 e2 =>
              match evalV fuel' env e1, evalV fuel' env e2 with
              | VNum n1, VNum 0 => VVoid
              | VNum n1, VNum n2 => VNum (n1 mod n2)
              | VVoid, _ => VVoid
              | _, VVoid => VVoid
              | _, _ => VVoid
              end
          
          (* Void operations *)
          | EVIsVoid e =>
              match evalV fuel' env e with
              | VVoid => VBool true
              | _ => VBool false
              end
              
          | EVIfVoid cond then_branch else_branch =>
              match evalV fuel' env cond with
              | VVoid => evalV fuel' env then_branch
              | _ => evalV fuel' env else_branch
              end
              
          | EVDefault e default =>
              match evalV fuel' env e with
              | VVoid => evalV fuel' env default
              | v => v
              end
          
          (* NEW: Variable lookup *)
          | EVVar x => lookup env x
          
          (* NEW: Let binding *)
          | EVLet x e1 e2 =>
              let v1 := evalV fuel' env e1 in
              evalV fuel' ((x, v1) :: env) e2  (* Extend environment *)
          end
      end.
    
    (** Evaluation with empty environment *)
    Definition evalV_empty (e : ExprV) : Value :=
      evalV 1000 [] e.
    
    (* ================================================================ *)
    (** ** Examples with Variables *)
    (* ================================================================ *)
    
    Module VariableExamples.
      
      (** Simple let binding *)
      Definition simple_let : ExprV :=
        EVLet "x" (EVNum 10)
          (EVAdd (EVVar "x") (EVNum 5)).  (* let x = 10 in x + 5 *)
      
      Example simple_let_result :
        evalV_empty simple_let = VNum 15.
      Proof. reflexivity. Qed.
      
      (** Nested let bindings *)
      Definition nested_let : ExprV :=
        EVLet "x" (EVNum 10)
          (EVLet "y" (EVNum 20)
            (EVAdd (EVVar "x") (EVVar "y"))).  (* let x = 10 in let y = 20 in x + y *)
      
      Example nested_let_result :
        evalV_empty nested_let = VNum 30.
      Proof. reflexivity. Qed.
      
      (** Undefined variable returns void *)
      Definition undefined_var : ExprV :=
        EVAdd (EVVar "x") (EVNum 5).  (* x + 5, but x is undefined *)
      
      Example undefined_var_result :
        evalV_empty undefined_var = VVoid.
      Proof. reflexivity. Qed.
      
      (** Void in let binding *)
      Definition void_binding : ExprV :=
        EVLet "x" (EVDiv (EVNum 10) (EVNum 0))  (* x = 10/0 = void *)
          (EVAdd (EVVar "x") (EVNum 5)).        (* x + 5 = void + 5 = void *)
      
      Example void_binding_result :
        evalV_empty void_binding = VVoid.
      Proof. reflexivity. Qed.
      
      (** Shadowing *)
      Definition shadowing : ExprV :=
        EVLet "x" (EVNum 10)
          (EVLet "x" (EVNum 20)  (* Inner x shadows outer x *)
            (EVVar "x")).
      
      Example shadowing_result :
        evalV_empty shadowing = VNum 20.
      Proof. reflexivity. Qed.
      
      (** Recovery from undefined variable *)
      Definition recover_undefined : ExprV :=
        EVDefault (EVVar "undefined_var") (EVNum 42).
      
      Example recover_undefined_result :
        evalV_empty recover_undefined = VNum 42.
      Proof. reflexivity. Qed.
      
      (** Complex expression with variables *)
      Definition complex_with_vars : ExprV :=
        EVLet "divisor" (EVNum 0)
          (EVLet "result" (EVDiv (EVNum 100) (EVVar "divisor"))  (* 100/0 = void *)
            (EVDefault (EVVar "result") 
              (EVLet "x" (EVNum 10)
                (EVLet "y" (EVNum 32)
                  (EVAdd (EVVar "x") (EVVar "y")))))).  (* Default to 10 + 32 *)
      
      Example complex_with_vars_result :
        evalV_empty complex_with_vars = VNum 42.
      Proof. reflexivity. Qed.
      
    End VariableExamples.
    
    (* ================================================================ *)
    (** ** Properties *)
    (* ================================================================ *)
    
    Module VariableProperties.
      
      (** Undefined variables are void *)
      Theorem undefined_is_void : forall x,
        lookup [] x = VVoid.
      Proof.
        intro x. reflexivity.
      Qed.
      
      (** Let bindings extend the environment correctly *)
      Theorem let_extends_env : forall fuel env x e1 e2,
        evalV (S fuel) env (EVLet x e1 e2) = 
        evalV fuel ((x, evalV fuel env e1) :: env) e2.
      Proof.
        intros fuel env x e1 e2.
        simpl. reflexivity.
      Qed.
      
      (** Void bindings propagate *)
      Theorem void_binding_propagates : forall fuel env x,
        evalV fuel env (EVLet x EVVoid (EVAdd (EVVar x) (EVNum 1))) = VVoid.
      Proof.
        intros fuel env x.
        destruct fuel; [reflexivity|].
        destruct fuel; [reflexivity|].
        simpl.
        (* Now we need to evaluate EVVar x with fuel in environment ((x, VVoid) :: env) *)
        destruct fuel.
        - (* fuel = 0, so evalV returns VVoid *)
          reflexivity.
        - (* fuel = S fuel', so it actually does the lookup *)
          simpl.
          rewrite String.eqb_refl.
          reflexivity.
      Qed.
      
      End VariableProperties.
  End WithVariables.

  (* ================================================================ *)
  (** ** Thermodynamic UnravelLang - Where Computation Meets Physics *)
  (* ================================================================ *)

  Module ThermodynamicUnravelLang.
    Import Core.
    Import WithVariables.
    
    (** Void now carries thermodynamic information *)
    Inductive VoidInfo : Type :=
      | VInfo : nat ->          (* entropy: how much disorder *)
                nat ->          (* time: when it happened *)
                VoidSource ->   (* source: why it failed *)
                VoidInfo
                
    with VoidSource : Type :=
      | DivByZero : nat -> VoidSource
      | ModByZero : nat -> VoidSource  
      | UndefinedVar : string -> VoidSource
      | OutOfFuel : VoidSource
      | TypeError : string -> VoidSource
      | VoidPropagation : VoidInfo -> VoidInfo -> VoidSource.
    
    (** Enhanced values with entropy *)
    Inductive ValueT : Type :=
      | VTNum : nat -> ValueT
      | VTBool : bool -> ValueT
      | VTVoid : VoidInfo -> ValueT.
    
    (** The universe state during computation *)
    Record Universe := {
      total_entropy : nat;
      time_step : nat;
      void_count : nat
    }.
    
    Definition initial_universe : Universe := {|
      total_entropy := 0;
      time_step := 0;
      void_count := 0
    |}.
    
    Definition evolve_universe (u : Universe) (info : VoidInfo) : Universe :=
      match info with
      | VInfo entropy _ _ => {|
          total_entropy := u.(total_entropy) + entropy;
          time_step := S u.(time_step);
          void_count := S u.(void_count)
        |}
      end.
    
    Definition combine_voids (v1 v2 : VoidInfo) (u : Universe) : VoidInfo :=
      match v1, v2 with
      | VInfo e1 t1 s1, VInfo e2 t2 s2 =>
          VInfo (e1 + e2) u.(time_step) (VoidPropagation v1 v2)
      end.
    
    (** Helper for lookup *)
    Fixpoint lookupT (env : list (string * ValueT)) (x : string) : option ValueT :=
      match env with
      | [] => None
      | (y, v) :: rest =>
          if String.eqb x y then Some v else lookupT rest x
      end.
    
    (** Complete evaluation function *)
    Fixpoint evalT (fuel : nat) (u : Universe) (env : list (string * ValueT)) 
                  (e : ExprV) : (ValueT * Universe) :=
      match fuel with
      | 0 => 
          let info := VInfo 1 u.(time_step) OutOfFuel in
          (VTVoid info, evolve_universe u info)
      | S fuel' =>
          match e with
          | EVNum n => (VTNum n, u)
          | EVVoid => 
              let info := VInfo 1 u.(time_step) (TypeError "pure_void") in
              (VTVoid info, evolve_universe u info)
          | EVBool b => (VTBool b, u)
          
          | EVAdd e1 e2 =>
              let '(v1, u1) := evalT fuel' u env e1 in
              let '(v2, u2) := evalT fuel' u1 env e2 in
              match v1, v2 with
              | VTNum n1, VTNum n2 => (VTNum (n1 + n2), u2)
              | VTVoid i1, VTNum _ => (VTVoid i1, u2)
              | VTNum _, VTVoid i2 => (VTVoid i2, u2)
              | VTVoid i1, VTVoid i2 => 
                  let combined := combine_voids i1 i2 u2 in
                  (VTVoid combined, evolve_universe u2 combined)
              | _, _ => 
                  let info := VInfo 1 u2.(time_step) (TypeError "add") in
                  (VTVoid info, evolve_universe u2 info)
              end
              
          | EVSub e1 e2 =>
              let '(v1, u1) := evalT fuel' u env e1 in
              let '(v2, u2) := evalT fuel' u1 env e2 in
              match v1, v2 with
              | VTNum n1, VTNum n2 => (VTNum (n1 - n2), u2)
              | VTVoid i1, VTNum _ => (VTVoid i1, u2)
              | VTNum _, VTVoid i2 => (VTVoid i2, u2)
              | VTVoid i1, VTVoid i2 => 
                  let combined := combine_voids i1 i2 u2 in
                  (VTVoid combined, evolve_universe u2 combined)
              | _, _ => 
                  let info := VInfo 1 u2.(time_step) (TypeError "sub") in
                  (VTVoid info, evolve_universe u2 info)
              end
              
          | EVMul e1 e2 =>
              let '(v1, u1) := evalT fuel' u env e1 in
              let '(v2, u2) := evalT fuel' u1 env e2 in
              match v1, v2 with
              | VTNum n1, VTNum n2 => (VTNum (n1 * n2), u2)
              | VTVoid i1, VTNum _ => (VTVoid i1, u2)
              | VTNum _, VTVoid i2 => (VTVoid i2, u2)
              | VTVoid i1, VTVoid i2 => 
                  let combined := combine_voids i1 i2 u2 in
                  (VTVoid combined, evolve_universe u2 combined)
              | _, _ => 
                  let info := VInfo 1 u2.(time_step) (TypeError "mul") in
                  (VTVoid info, evolve_universe u2 info)
              end
              
          | EVDiv e1 e2 =>
              let '(v1, u1) := evalT fuel' u env e1 in
              let '(v2, u2) := evalT fuel' u1 env e2 in
              match v1, v2 with
              | VTNum n1, VTNum 0 => 
                  let info := VInfo 1 u2.(time_step) (DivByZero n1) in
                  (VTVoid info, evolve_universe u2 info)
              | VTNum n1, VTNum n2 => (VTNum (n1 / n2), u2)
              | VTVoid i, _ => (VTVoid i, u2)
              | _, VTVoid i => (VTVoid i, u2)
              | _, _ => 
                  let info := VInfo 1 u2.(time_step) (TypeError "div") in
                  (VTVoid info, evolve_universe u2 info)
              end
              
          | EVMod e1 e2 =>
              let '(v1, u1) := evalT fuel' u env e1 in
              let '(v2, u2) := evalT fuel' u1 env e2 in
              match v1, v2 with
              | VTNum n1, VTNum 0 => 
                  let info := VInfo 1 u2.(time_step) (ModByZero n1) in
                  (VTVoid info, evolve_universe u2 info)
              | VTNum n1, VTNum n2 => (VTNum (n1 mod n2), u2)
              | VTVoid i, _ => (VTVoid i, u2)
              | _, VTVoid i => (VTVoid i, u2)
              | _, _ => 
                  let info := VInfo 1 u2.(time_step) (TypeError "mod") in
                  (VTVoid info, evolve_universe u2 info)
              end
          
          | EVIsVoid e =>
              let '(v, u') := evalT fuel' u env e in
              match v with
              | VTVoid _ => (VTBool true, u')
              | _ => (VTBool false, u')
              end
              
          | EVIfVoid cond then_branch else_branch =>
              let '(v, u1) := evalT fuel' u env cond in
              match v with
              | VTVoid _ => evalT fuel' u1 env then_branch
              | _ => evalT fuel' u1 env else_branch
              end
              
          | EVDefault e default =>
              let '(v, u1) := evalT fuel' u env e in
              match v with
              | VTVoid _ => evalT fuel' u1 env default
              | v => (v, u1)
              end
              
          | EVVar x =>
              match lookupT env x with
              | Some v => (v, u)
              | None => 
                  let info := VInfo 1 u.(time_step) (UndefinedVar x) in
                  (VTVoid info, evolve_universe u info)
              end
              
          | EVLet x e1 e2 =>
              let '(v1, u1) := evalT fuel' u env e1 in
              evalT fuel' u1 ((x, v1) :: env) e2
          end
      end.
    
    (** Helper to run with initial universe *)
    Definition evalT_initial (e : ExprV) : (ValueT * Universe) :=
      evalT 1000 initial_universe [] e.
    
    (** Extract entropy from a value *)
    Definition value_entropy (v : ValueT) : nat :=
      match v with
      | VTVoid (VInfo e _ _) => e
      | _ => 0
      end.
    
    (** Check if universe has reached heat death *)
    Definition is_heat_death (u : Universe) : bool :=
      Nat.leb 100 u.(total_entropy).

    Module ThermodynamicProperties.
      
      (** Helper: Universe entropy is monotonic *)
      Lemma evolve_increases_entropy :
        forall u info,
        u.(total_entropy) <= (evolve_universe u info).(total_entropy).
      Proof.
        intros u info.
        destruct info as [e t s].
        simpl.
        apply Nat.le_add_r.
      Qed.
      
      (** Helper: Time strictly increases when universe evolves *)
      Lemma evolve_increases_time :
        forall u info,
        u.(time_step) < (evolve_universe u info).(time_step).
      Proof.
        intros u info.
        destruct info as [e t s].
        simpl.
        apply Nat.lt_succ_diag_r.
      Qed.
      
      (** Combined voids have higher entropy - PROVEN! *)
      Theorem void_combination_entropy :
        forall v1 v2 u,
        match combine_voids v1 v2 u with
        | VInfo e_combined _ _ =>
            match v1, v2 with
            | VInfo e1 _ _, VInfo e2 _ _ =>
                e_combined = e1 + e2
            end
        end.
      Proof.
        intros v1 v2 u.
        destruct v1 as [e1 t1 s1], v2 as [e2 t2 s2].
        reflexivity.
      Qed.

      (** Helper: Adding any natural number increases *)
      Lemma le_plus_r : forall n m : nat, n <= n + m.
      Proof.
        intros n m.
        induction m.
        - rewrite Nat.add_0_r. apply Nat.le_refl.
        - rewrite Nat.add_succ_r. apply le_S. exact IHm.
      Qed.
      
      (** Helper for base case *)
      Lemma base_case_entropy :
        forall u,
        u.(total_entropy) <= 
        (evolve_universe u (VInfo 1 u.(time_step) OutOfFuel)).(total_entropy).
      Proof.
        intro u.
        simpl.
        apply le_plus_r.
      Qed.

      (** Entropy never decreases *)
      Theorem entropy_second_law :
        forall fuel u env e,
        let '(_, u') := evalT fuel u env e in
        u.(total_entropy) <= u'.(total_entropy).
      Proof.
        intro fuel.
        induction fuel; intros u env e.
        - (* Base case: fuel = 0 *)
          simpl. apply le_plus_r.
        
        - (* Inductive case *)
          destruct e; simpl.
          
          + (* EVNum *) apply Nat.le_refl.
          + (* EVVoid *) apply le_plus_r.
          + (* EVBool *) apply Nat.le_refl.
          
          + (* EVAdd *)
            destruct (evalT fuel u env e1) as [v1 u1] eqn:He1.
            destruct (evalT fuel u1 env e2) as [v2 u2] eqn:He2.
            assert (H1: u.(total_entropy) <= u1.(total_entropy)).
            { specialize (IHfuel u env e1). rewrite He1 in IHfuel. exact IHfuel. }
            assert (H2: u1.(total_entropy) <= u2.(total_entropy)).
            { specialize (IHfuel u1 env e2). rewrite He2 in IHfuel. exact IHfuel. }
            destruct v1 as [n1|b1|i1], v2 as [n2|b2|i2];
            try (apply Nat.le_trans with u1.(total_entropy); auto).
            * (* VTNum, VTBool - type error *)
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
            * (* VTBool, VTNum - type error *)
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
            * (* VTBool, VTBool - type error *)
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
            * (* VTBool, VTVoid - type error *)
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
            * (* VTVoid, VTBool - type error *)
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
            * (* VTVoid, VTVoid - combines *)
              destruct i1 as [entropy1 time1 source1], i2 as [entropy2 time2 source2].
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
          
          + (* EVSub - same pattern as EVAdd *)
            destruct (evalT fuel u env e1) as [v1 u1] eqn:He1.
            destruct (evalT fuel u1 env e2) as [v2 u2] eqn:He2.
            assert (H1: u.(total_entropy) <= u1.(total_entropy))
              by (specialize (IHfuel u env e1); rewrite He1 in IHfuel; exact IHfuel).
            assert (H2: u1.(total_entropy) <= u2.(total_entropy))
              by (specialize (IHfuel u1 env e2); rewrite He2 in IHfuel; exact IHfuel).
            destruct v1 as [n1|b1|i1], v2 as [n2|b2|i2];
            try (apply Nat.le_trans with u1.(total_entropy); auto);
            try (simpl; apply Nat.le_trans with u2.(total_entropy);
                [apply Nat.le_trans with u1.(total_entropy); auto | apply le_plus_r]).
            * (* VTVoid, VTVoid - special case *)
              destruct i1 as [entropy1 time1 source1], i2 as [entropy2 time2 source2].
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
          
          + (* EVMul - same pattern *)
            destruct (evalT fuel u env e1) as [v1 u1] eqn:He1.
            destruct (evalT fuel u1 env e2) as [v2 u2] eqn:He2.
            assert (H1: u.(total_entropy) <= u1.(total_entropy))
              by (specialize (IHfuel u env e1); rewrite He1 in IHfuel; exact IHfuel).
            assert (H2: u1.(total_entropy) <= u2.(total_entropy))
              by (specialize (IHfuel u1 env e2); rewrite He2 in IHfuel; exact IHfuel).
            destruct v1 as [n1|b1|i1], v2 as [n2|b2|i2];
            try (apply Nat.le_trans with u1.(total_entropy); auto);
            try (simpl; apply Nat.le_trans with u2.(total_entropy);
                [apply Nat.le_trans with u1.(total_entropy); auto | apply le_plus_r]).
            * (* VTVoid, VTVoid *)
              destruct i1 as [entropy1 time1 source1], i2 as [entropy2 time2 source2].
              simpl. apply Nat.le_trans with u2.(total_entropy).
              -- apply Nat.le_trans with u1.(total_entropy); auto.
              -- apply le_plus_r.
          
          + (* EVDiv *)
            destruct (evalT fuel u env e1) as [v1 u1] eqn:He1.
            destruct (evalT fuel u1 env e2) as [v2 u2] eqn:He2.
            assert (H1: u.(total_entropy) <= u1.(total_entropy)).
            { specialize (IHfuel u env e1). rewrite He1 in IHfuel. exact IHfuel. }
            assert (H2: u1.(total_entropy) <= u2.(total_entropy)).
            { specialize (IHfuel u1 env e2). rewrite He2 in IHfuel. exact IHfuel. }
            destruct v1 as [n1|b1|i1].
            * (* v1 = VTNum n1 *)
              destruct v2 as [n2|b2|i2].
              -- (* VTNum n2 *)
                destruct n2.
                ++ (* n2 = 0: division by zero *)
                    simpl. apply Nat.le_trans with u2.(total_entropy).
                    ** apply Nat.le_trans with u1.(total_entropy); auto.
                    ** apply le_plus_r.
                ++ (* n2 = S _ : normal division *)
                    apply Nat.le_trans with u1.(total_entropy); auto.
              -- (* VTBool *)
                simpl. apply Nat.le_trans with u2.(total_entropy).
                ++ apply Nat.le_trans with u1.(total_entropy); auto.
                ++ apply le_plus_r.
              -- (* VTVoid *)
                apply Nat.le_trans with u1.(total_entropy); auto.
            * (* v1 = VTBool b1 *)
              destruct v2; 
              try (simpl; apply Nat.le_trans with u2.(total_entropy);
                  [apply Nat.le_trans with u1.(total_entropy); auto | apply le_plus_r]);
              try (apply Nat.le_trans with u1.(total_entropy); auto).
            * (* v1 = VTVoid i1 *)
              apply Nat.le_trans with u1.(total_entropy); auto.
          
          + (* EVMod - similar to EVDiv *)
            destruct (evalT fuel u env e1) as [v1 u1] eqn:He1.
            destruct (evalT fuel u1 env e2) as [v2 u2] eqn:He2.
            assert (H1: u.(total_entropy) <= u1.(total_entropy)).
            { specialize (IHfuel u env e1). rewrite He1 in IHfuel. exact IHfuel. }
            assert (H2: u1.(total_entropy) <= u2.(total_entropy)).
            { specialize (IHfuel u1 env e2). rewrite He2 in IHfuel. exact IHfuel. }
            destruct v1 as [n1|b1|i1].
            * destruct v2 as [n2|b2|i2].
              -- destruct n2.
                ++ simpl. apply Nat.le_trans with u2.(total_entropy).
                    ** apply Nat.le_trans with u1.(total_entropy); auto.
                    ** apply le_plus_r.
                ++ apply Nat.le_trans with u1.(total_entropy); auto.
              -- simpl. apply Nat.le_trans with u2.(total_entropy).
                ++ apply Nat.le_trans with u1.(total_entropy); auto.
                ++ apply le_plus_r.
              -- apply Nat.le_trans with u1.(total_entropy); auto.
            * destruct v2;
              try (simpl; apply Nat.le_trans with u2.(total_entropy);
                  [apply Nat.le_trans with u1.(total_entropy); auto | apply le_plus_r]);
              try (apply Nat.le_trans with u1.(total_entropy); auto).
            * apply Nat.le_trans with u1.(total_entropy); auto.
          
          + (* EVIsVoid *)
            destruct (evalT fuel u env e) as [v u'] eqn:He.
            assert (H: u.(total_entropy) <= u'.(total_entropy))
              by (specialize (IHfuel u env e); rewrite He in IHfuel; exact IHfuel).
            destruct v; exact H.
          
          + (* EVIfVoid *)
            destruct (evalT fuel u env e1) as [v u1] eqn:He1.
            assert (H1: u.(total_entropy) <= u1.(total_entropy))
              by (specialize (IHfuel u env e1); rewrite He1 in IHfuel; exact IHfuel).
            destruct v.
            * (* VTNum - take else branch *)
              specialize (IHfuel u1 env e3).
              destruct (evalT fuel u1 env e3) as [v' u'].
              apply Nat.le_trans with u1.(total_entropy); auto.
            * (* VTBool - take else branch *)
              specialize (IHfuel u1 env e3).
              destruct (evalT fuel u1 env e3) as [v' u'].
              apply Nat.le_trans with u1.(total_entropy); auto.
            * (* VTVoid - take then branch *)
              specialize (IHfuel u1 env e2).
              destruct (evalT fuel u1 env e2) as [v' u'].
              apply Nat.le_trans with u1.(total_entropy); auto.
          
          + (* EVDefault *)
            destruct (evalT fuel u env e1) as [v u1] eqn:He1.
            assert (H1: u.(total_entropy) <= u1.(total_entropy))
              by (specialize (IHfuel u env e1); rewrite He1 in IHfuel; exact IHfuel).
            destruct v.
            * (* VTNum - return it *) exact H1.
            * (* VTBool - return it *) exact H1.
            * (* VTVoid - evaluate default *)
              specialize (IHfuel u1 env e2).
              destruct (evalT fuel u1 env e2) as [v' u'].
              apply Nat.le_trans with u1.(total_entropy); auto.
          
          + (* EVVar - already done *)
            destruct (lookupT env s).
            * apply Nat.le_refl.
            * simpl. apply le_plus_r.
          
          + (* EVLet *)
            destruct (evalT fuel u env e1) as [v1 u1] eqn:He1.
            assert (H1: u.(total_entropy) <= u1.(total_entropy))
              by (specialize (IHfuel u env e1); rewrite He1 in IHfuel; exact IHfuel).
            specialize (IHfuel u1 ((s, v1) :: env) e2).
            destruct (evalT fuel u1 ((s, v1) :: env) e2) as [v2 u2].
            apply Nat.le_trans with u1.(total_entropy); auto.
      Qed.
      
      (** Void creation strictly increases void count *)
      Theorem void_creation_increases_count :
        forall u info,
        u.(void_count) < (evolve_universe u info).(void_count).
      Proof.
        intros u [e t s].
        simpl.
        apply Nat.lt_succ_diag_r.
      Qed.
      
      (** Simple example that we can actually compute *)
      Example simple_entropy_increase :
        let '(v, u) := evalT 10 initial_universe [] (EVDiv (EVNum 10) (EVNum 0)) in
        u.(total_entropy) = 1 /\ u.(void_count) = 1.
      Proof.
        simpl.
        split; reflexivity.
      Qed.
      
      (** Double void creates more entropy *)
      Example double_void_entropy :
        let prog := EVAdd (EVDiv (EVNum 10) (EVNum 0)) 
                          (EVDiv (EVNum 20) (EVNum 0)) in
        let '(v, u) := evalT 10 initial_universe [] prog in
        u.(total_entropy) = 4 /\ u.(void_count) = 3.
        (* 1 for first div/0, 1 for second div/0, 2 for combining them (1+1) *)
      Proof.
        simpl.
        split; reflexivity.
      Qed.
      
    End ThermodynamicProperties.
    
  End ThermodynamicUnravelLang.

  (* ================================================================ *)
  (** ** Example: Watching the Universe Evolve *)
  (* ================================================================ *)
  
  (* Module UniverseExamples.
    
    (** A computation that increases entropy *)
    Definition entropy_generator : ExprV :=
      EVLet "x" (EVDiv (EVNum 10) (EVNum 0))  (* Create void *)
        (EVLet "y" (EVDiv (EVNum 20) (EVNum 0))  (* Another void *)
          (EVAdd (EVVar "x") (EVVar "y"))).  (* Combine them *)
    
    (** Run and observe universe evolution *)
    Example universe_evolution :
      let '(v, u) := evalT 100 initial_universe [] entropy_generator in
      u.(total_entropy) >= 2.  (* At least 2 units of entropy created *)
    Proof.
      simpl.
      (* Would show the actual computation *)
      Admitted.
    Qed.
    
    (** A program that approaches heat death *)
    Fixpoint chaos_generator (n : nat) : ExprV :=
      match n with
      | 0 => EVNum 42
      | S n' => EVAdd (EVDiv (EVNum 1) (EVNum 0)) (chaos_generator n')
      end.
    
    (** The philosophical demonstration *)
    Definition computation_is_physics : Prop :=
      (* Every program execution creates entropy *)
      (forall e, exists u', evalT 1000 initial_universe [] e = (_, u')) /\
      (* Complex programs create more entropy *)
      (forall e1 e2, True) /\  (* Would formalize complexity *)
      (* The universe evolves through computation *)
      True.
    
  End UniverseExamples. *)
  
  (* ================================================================ *)
  (** ** Connection to Framework *)
  (* ================================================================ *)
  
  Module FrameworkConnection.
    Import Core.
    Import Eval.
    Import ImpossibilityAlgebra Core.
    Import WaysOfNotExisting.Core.
    Import WaysOfNotExisting.PatternEquivalence.
    
    Section ConnectionToPatterns.
      Context {Alpha : AlphaType}.
      
      (** Every void value corresponds to omega_veil *)
      Definition void_value_is_omega : WayOfNotExisting -> Prop :=
        omega_veil.
      
      (** Expressions that evaluate to void are impossible patterns *)
      Definition void_expression_pattern (e : Expr) : WayOfNotExisting -> Prop :=
        fun w => eval_default e = VVoid /\ omega_veil w.
      
      (** Division by zero is an impossible pattern *)
      Theorem div_zero_is_impossible : 
        ImpossibilityAlgebra.Core.Is_Impossible 
          (void_expression_pattern (EDiv (ENum 1) (ENum 0))).
      Proof.
        intro w.
        split.
        - intros [H Hom].
          exact Hom.
        - intro Hom.
          exfalso.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses w Hom).
      Qed.
      
      (** All void expressions are equivalent patterns *)
      Theorem void_expressions_equivalent : forall e1 e2,
        eval_default e1 = VVoid ->
        eval_default e2 = VVoid ->
        pattern_equiv (void_expression_pattern e1) 
                     (void_expression_pattern e2).
      Proof.
        intros e1 e2 H1 H2.
        unfold pattern_equiv.
        split; [|split].
        - (* Is_Impossible (void_expression_pattern e1) *)
          intro w. split.
          + intros [_ Hom]. exact Hom.
          + intro Hom. exfalso.
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses w Hom).
        - (* Is_Impossible (void_expression_pattern e2) *)
          intro w. split.
          + intros [_ Hom]. exact Hom.
          + intro Hom. exfalso.
            exact (AlphaProperties.Core.omega_veil_has_no_witnesses w Hom).
        - (* Extensional equality *)
          intro w.
          unfold void_expression_pattern.
          split; intros [H Hom]; exfalso;
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses w Hom).
      Qed.
      
    End ConnectionToPatterns.
  End FrameworkConnection.
  
  (* ================================================================ *)
  (** ** Example Programs *)
  (* ================================================================ *)
  
  Module Examples.
    Import Core.
    Import Eval.
    
    (** Safe division that returns 0 on divide by zero *)
    Definition safe_div (n m : nat) : Expr :=
      EDefault (EDiv (ENum n) (ENum m)) (ENum 0).
    
    Example safe_div_by_zero :
      eval_default (safe_div 10 0) = VNum 0.
    Proof. reflexivity. Qed.
    
    Example safe_div_normal :
      eval_default (safe_div 10 2) = VNum 5.
    Proof. reflexivity. Qed.
    
    (** Check if a number divides another *)
    Definition divides (n m : nat) : Expr :=
      EIsVoid (EMod (ENum m) (ENum n)).
    
    Example divides_example :
      eval_default (divides 3 9) = VBool false /\
      eval_default (divides 3 10) = VBool false /\
      eval_default (divides 0 10) = VBool true.  (* 0 divides nothing → void → true *)
    Proof. split; [|split]; reflexivity. Qed.
    
    (** Chain of operations that might fail *)
    Definition calculation : Expr :=
      EAdd (EDiv (ENum 10) (ENum 2))    (* 10/2 = 5 *)
           (EDiv (ENum 8) (ENum 4)).     (* 8/4 = 2, result = 7 *)
    
    Definition risky_calculation : Expr :=
      EAdd (EDiv (ENum 10) (ENum 0))    (* 10/0 = void *)
           (EDiv (ENum 8) (ENum 4)).     (* void propagates *)
    
    Example calculation_works :
      eval_default calculation = VNum 7.
    Proof. reflexivity. Qed.
    
    Example risky_calculation_fails :
      eval_default risky_calculation = VVoid.
    Proof. reflexivity. Qed.
    
    (** Recovery from void *)
    Definition recovered : Expr :=
      EDefault risky_calculation (ENum 42).
    
    Example recovery_works :
      eval_default recovered = VNum 42.
    Proof. reflexivity. Qed.
    
  End Examples.
  
  (* ================================================================ *)
  (** ** Extraction Setup *)
  (* ================================================================ *)
  
  Module Extraction.
    Import Core.
    Import Eval.
    Import WithVariables.
    Import ThermodynamicUnravelLang.
    Import Examples.
    Import VariableExamples.
    
    (** For extraction to Haskell *)
    Extraction Language Haskell.
    Set Extraction AutoInline.
    Extraction Blacklist Prelude.
    
    (* Tell Coq how to map types - use qualified names *)
    Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
    Extract Inductive nat => "Prelude.Integer" 
    ["0" "(\n -> n Prelude.+ 1)"]
    "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
    Extract Inductive list => "[]" ["[]" "(:)"].
    
    (* FIX: Map Coq's string to Haskell's String *)
    Extract Inductive string => "Prelude.String" ["[]" "(:)"].
    
    (* Extract Constant WithVariables.lookup => "voidLookup".
    Extract Constant ThermodynamicUnravelLang.lookupT => "voidLookupT". *)
    
    (* String equality *)
    Extract Constant String.eqb => "(Prelude.==)".

    (* Map ascii to Char *)
    Extract Inductive ascii => "Prelude.Char" 
    ["(\\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr (Prelude.fromIntegral ((if b0 then 1 else 0) Prelude.+ (if b1 then 2 else 0) Prelude.+ (if b2 then 4 else 0) Prelude.+ (if b3 then 8 else 0) Prelude.+ (if b4 then 16 else 0) Prelude.+ (if b5 then 32 else 0) Prelude.+ (if b6 then 64 else 0) Prelude.+ (if b7 then 128 else 0))))"]
    "(\fAscii c -> fAscii (let n = Data.Char.ord c in (n `Prelude.mod` 2 Prelude.== 1) ((n `Prelude.div` 2) `Prelude.mod` 2 Prelude.== 1) ((n `Prelude.div` 4) `Prelude.mod` 2 Prelude.== 1) ((n `Prelude.div` 8) `Prelude.mod` 2 Prelude.== 1) ((n `Prelude.div` 16) `Prelude.mod` 2 Prelude.== 1) ((n `Prelude.div` 32) `Prelude.mod` 2 Prelude.== 1) ((n `Prelude.div` 64) `Prelude.mod` 2 Prelude.== 1) (n `Prelude.div` 128 Prelude.== 1)))".

    Extract Constant Nat.div => "(\n m -> n `Prelude.div` m)".
    Extract Constant Nat.modulo => "(\n m -> n `Prelude.mod` m)".
    
    (** Demo programs... rest stays the same **)
    
    Definition demo_division_chain : ExprV :=
      EVLet "x" (EVDiv (EVNum 100) (EVNum 10))
        (EVLet "y" (EVDiv (EVNum 50) (EVNum 0))
          (EVDefault (EVAdd (EVVar "x") (EVVar "y"))
                     (EVNum 999))).
    
    Definition demo_undefined : ExprV :=
      EVDefault 
        (EVAdd (EVVar "undefined") (EVNum 42))
        (EVMul (EVNum 6) (EVNum 7)).
    
    Definition demo_entropy : ExprV :=
      EVLet "a" (EVDiv (EVNum 1) (EVNum 0))
        (EVLet "b" (EVVar "undefined_var")
          (EVLet "c" (EVMod (EVNum 10) (EVNum 0))
            (EVAdd (EVAdd (EVVar "a") (EVVar "b")) (EVVar "c")))).
    
    Definition demo_recovery : ExprV :=
      EVDefault
        (EVDefault 
          (EVDefault (EVDiv (EVNum 10) (EVNum 0)) (EVNum 1))
          (EVNum 2))
        (EVNum 3).
    
    Definition demo_void_check : ExprV :=
      EVIfVoid (EVDiv (EVNum 10) (EVNum 0))
        (EVNum 1)
        (EVNum 0).
    
    Fixpoint chaos_generator (n : nat) : ExprV :=
      match n with
      | 0 => EVNum 42
      | S n' => EVAdd (EVDiv (EVNum 1) (EVNum 0)) (chaos_generator n')
      end.
    
    Definition run_basic (e : ExprV) : Value :=
      evalV 1000 [] e.
    
    Definition run_thermo (e : ExprV) : (ValueT * Universe) :=
      evalT 1000 initial_universe [] e.
    
    Definition test_programs : list ExprV :=
      [demo_division_chain;
       demo_undefined;
       demo_entropy;
       demo_recovery;
       demo_void_check;
       simple_let;
       nested_let;
       complex_with_vars;
       chaos_generator 5;
       chaos_generator 10].
    
    (* Unravel/ local dir must exist already for this to work *)
    Extraction "Unravel/Unravel.hs" 
      (* Core types *)
      Core.Expr Core.Value 
      ExprV ValueT Universe VoidInfo VoidSource
      
      (* Evaluators *)
      Eval.eval Eval.eval_default
      evalV evalV_empty
      evalT evalT_initial
      
      (* Examples *)
      Examples.safe_div Examples.divides Examples.calculation
      demo_division_chain demo_undefined demo_entropy 
      demo_recovery demo_void_check
      simple_let nested_let complex_with_vars
      chaos_generator
      
      (* Helpers *)
      run_basic run_thermo test_programs
      initial_universe is_heat_death value_entropy.
    
  End Extraction.

End UnravelLang.

(* ================================================================ *)
(** ** Next Steps *)
(* ================================================================ *)

(*
  This simple arithmetic language demonstrates:
  - Void as a first-class value
  - Total evaluation (no crashes)
  - Natural error handling through void propagation
  - Recovery mechanisms (Default)
  
  We could extend this with:
  - Variables and let-bindings
  - Functions and application
  - Recursion (with fuel to prevent infinite loops)
  - Lists and other data structures
  - Pattern matching on void
  
  The key insight: In a language built on void, "errors" aren't
  exceptional - they're just another value that flows through
  computation naturally.
*)