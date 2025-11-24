
val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val leb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int*int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

val eqb : string -> string -> bool

module UnravelLang :
 sig
  module Core :
   sig
    type coq_Expr =
    | ENum of int
    | EVoid
    | EBool of bool
    | EAdd of coq_Expr * coq_Expr
    | ESub of coq_Expr * coq_Expr
    | EMul of coq_Expr * coq_Expr
    | EDiv of coq_Expr * coq_Expr
    | EMod of coq_Expr * coq_Expr
    | EIsVoid of coq_Expr
    | EIfVoid of coq_Expr * coq_Expr * coq_Expr
    | EDefault of coq_Expr * coq_Expr

    type coq_Value =
    | VNum of int
    | VBool of bool
    | VVoid

    val is_void : coq_Value -> bool

    val value_to_nat_default : coq_Value -> int -> int

    val value_to_bool_default : coq_Value -> bool -> bool
   end

  module Eval :
   sig
    val eval : int -> Core.coq_Expr -> Core.coq_Value

    val eval_default : Core.coq_Expr -> Core.coq_Value
   end

  module WithVariables :
   sig
    type coq_ExprV =
    | EVNum of int
    | EVVoid
    | EVBool of bool
    | EVAdd of coq_ExprV * coq_ExprV
    | EVSub of coq_ExprV * coq_ExprV
    | EVMul of coq_ExprV * coq_ExprV
    | EVDiv of coq_ExprV * coq_ExprV
    | EVMod of coq_ExprV * coq_ExprV
    | EVIsVoid of coq_ExprV
    | EVIfVoid of coq_ExprV * coq_ExprV * coq_ExprV
    | EVDefault of coq_ExprV * coq_ExprV
    | EVVar of string
    | EVLet of string * coq_ExprV * coq_ExprV

    type coq_Env = (string*Core.coq_Value) list

    val lookup : coq_Env -> string -> Core.coq_Value

    val evalV : int -> coq_Env -> coq_ExprV -> Core.coq_Value

    val evalV_empty : coq_ExprV -> Core.coq_Value

    module VariableExamples :
     sig
      val simple_let : coq_ExprV

      val nested_let : coq_ExprV

      val undefined_var : coq_ExprV

      val void_binding : coq_ExprV

      val shadowing : coq_ExprV

      val recover_undefined : coq_ExprV

      val complex_with_vars : coq_ExprV
     end
   end

  module ThermodynamicUnravelLang :
   sig
    type coq_VoidInfo =
    | VInfo of int * int * coq_VoidSource
    and coq_VoidSource =
    | DivByZero of int
    | ModByZero of int
    | UndefinedVar of string
    | OutOfFuel
    | TypeError of string
    | VoidPropagation of coq_VoidInfo * coq_VoidInfo

    type coq_ValueT =
    | VTNum of int
    | VTBool of bool
    | VTVoid of coq_VoidInfo

    type coq_Universe = { total_entropy : int; time_step : int;
                          void_count : int }

    val total_entropy : coq_Universe -> int

    val time_step : coq_Universe -> int

    val void_count : coq_Universe -> int

    val initial_universe : coq_Universe

    val evolve_universe : coq_Universe -> coq_VoidInfo -> coq_Universe

    val combine_voids :
      coq_VoidInfo -> coq_VoidInfo -> coq_Universe -> coq_VoidInfo

    val lookupT : (string*coq_ValueT) list -> string -> coq_ValueT option

    val evalT :
      int -> coq_Universe -> (string*coq_ValueT) list ->
      WithVariables.coq_ExprV -> coq_ValueT*coq_Universe

    val evalT_initial : WithVariables.coq_ExprV -> coq_ValueT*coq_Universe

    val value_entropy : coq_ValueT -> int

    val is_heat_death : coq_Universe -> bool
   end

  module Examples :
   sig
    val safe_div : int -> int -> Core.coq_Expr

    val divides : int -> int -> Core.coq_Expr

    val calculation : Core.coq_Expr

    val risky_calculation : Core.coq_Expr

    val recovered : Core.coq_Expr
   end

  module ExtractionOcaml :
   sig
    val chaos_generator : int -> WithVariables.coq_ExprV

    module Runner :
     sig
      val test_simple : Core.coq_Value

      val test_void : Core.coq_Value

      val test_recovery : Core.coq_Value

      val test_let : Core.coq_Value

      val test_thermo :
        ThermodynamicUnravelLang.coq_ValueT*ThermodynamicUnravelLang.coq_Universe

      val get_entropy : WithVariables.coq_ExprV -> int
     end
   end
 end
