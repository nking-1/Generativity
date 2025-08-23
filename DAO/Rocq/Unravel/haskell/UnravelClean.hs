-- UnravelClean.hs
module UnravelClean where

import qualified Prelude

-- Option type (Maybe in Haskell)
data Option a = Some a | None
  deriving (Prelude.Eq, Prelude.Show)

-- Product type (tuple)
data Prod a b = Pair a b
  deriving (Prelude.Eq, Prelude.Show)

-- Arithmetic operations
-- These are straightforward since we're using Integer

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add = (Prelude.+)

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul = (Prelude.*)

-- Saturating subtraction (never goes below 0)
sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub n m = Prelude.max 0 (n Prelude.- m)

-- Another version of saturating subtraction (same behavior)
sub0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub0 = sub  -- They appear to be the same

-- Less than or equal
leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb = (Prelude.<=)

-- Division and modulo together
divmod :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> 
          Prelude.Integer -> Prod Prelude.Integer Prelude.Integer
divmod x y q u =
  -- This appears to be doing division with a quotient accumulator
  -- But we can simplify to just compute it directly
  if y Prelude.== 0 
  then Pair q u  -- Avoid division by zero
  else let (quot, rem) = Prelude.divMod x y
       in Pair quot rem

-- Division
div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (Prelude.div)

-- Modulo
modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo = (Prelude.mod)

-- String equality
eqb :: Prelude.String -> Prelude.String -> Prelude.Bool
eqb = (Prelude.==)


-- Expression type
data Expr = 
    ENum Prelude.Integer
  | EVoid
  | EBool Prelude.Bool
  | EAdd Expr Expr
  | ESub Expr Expr
  | EMul Expr Expr
  | EDiv Expr Expr
  | EMod Expr Expr
  | EIsVoid Expr
  | EIfVoid Expr Expr Expr
  | EDefault Expr Expr
  deriving (Prelude.Eq, Prelude.Show)

-- Value type
data Value =
    VNum Prelude.Integer
  | VBool Prelude.Bool
  | VVoid
  deriving (Prelude.Eq, Prelude.Show)

-- Core evaluation function
eval :: Prelude.Integer -> Expr -> Value
eval fuel e =
  if fuel Prelude.== 0 
  then VVoid  -- Out of fuel
  else 
    let fuel' = fuel Prelude.- 1 in
    case e of
      ENum n -> VNum n
      EVoid -> VVoid
      EBool b -> VBool b
      
      EAdd e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum n2) -> VNum (n1 Prelude.+ n2)
          _ -> VVoid
      
      ESub e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum n2) -> VNum (Prelude.max 0 (n1 Prelude.- n2))  -- Saturating
          _ -> VVoid
      
      EMul e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum n2) -> VNum (n1 Prelude.* n2)
          _ -> VVoid
      
      EDiv e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum 0) -> VVoid  -- Division by zero
          (VNum n1, VNum n2) -> VNum (n1 `Prelude.div` n2)
          _ -> VVoid
      
      EMod e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum 0) -> VVoid  -- Modulo by zero
          (VNum n1, VNum n2) -> VNum (n1 `Prelude.mod` n2)
          _ -> VVoid
      
      EIsVoid e0 ->
        case eval fuel' e0 of
          VVoid -> VBool Prelude.True
          _ -> VBool Prelude.False
      
      EIfVoid cond then_branch else_branch ->
        case eval fuel' cond of
          VVoid -> eval fuel' then_branch
          _ -> eval fuel' else_branch
      
      EDefault e0 default0 ->
        case eval fuel' e0 of
          VVoid -> eval fuel' default0
          v -> v

-- Default evaluation with fuel = 1000
eval_default :: Expr -> Value
eval_default = eval 1000

-- Expression with variables
data ExprV =
    EVNum Prelude.Integer
  | EVVoid
  | EVBool Prelude.Bool
  | EVAdd ExprV ExprV
  | EVSub ExprV ExprV
  | EVMul ExprV ExprV
  | EVDiv ExprV ExprV
  | EVMod ExprV ExprV
  | EVIsVoid ExprV
  | EVIfVoid ExprV ExprV ExprV
  | EVDefault ExprV ExprV
  | EVVar Prelude.String
  | EVLet Prelude.String ExprV ExprV
  deriving (Prelude.Eq, Prelude.Show)

-- Environment type
type Env = [(Prelude.String, Value)]

-- Lookup variable in environment
lookup :: Env -> Prelude.String -> Value
lookup [] x = VVoid  -- Undefined variable returns void
lookup ((y, v) : rest) x =
  if x Prelude.== y
  then v
  else lookup rest x

-- Evaluation with environment
evalV :: Prelude.Integer -> Env -> ExprV -> Value
evalV fuel env e =
  if fuel Prelude.== 0
  then VVoid
  else
    let fuel' = fuel Prelude.- 1 in
    case e of
      EVNum n -> VNum n
      EVVoid -> VVoid
      EVBool b -> VBool b
      
      EVAdd e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum n2) -> VNum (n1 Prelude.+ n2)
          _ -> VVoid
      
      EVSub e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum n2) -> VNum (Prelude.max 0 (n1 Prelude.- n2))
          _ -> VVoid
      
      EVMul e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum n2) -> VNum (n1 Prelude.* n2)
          _ -> VVoid
      
      EVDiv e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum 0) -> VVoid
          (VNum n1, VNum n2) -> VNum (n1 `Prelude.div` n2)
          _ -> VVoid
      
      EVMod e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum 0) -> VVoid
          (VNum n1, VNum n2) -> VNum (n1 `Prelude.mod` n2)
          _ -> VVoid
      
      EVIsVoid e0 ->
        case evalV fuel' env e0 of
          VVoid -> VBool Prelude.True
          _ -> VBool Prelude.False
      
      EVIfVoid cond then_branch else_branch ->
        case evalV fuel' env cond of
          VVoid -> evalV fuel' env then_branch
          _ -> evalV fuel' env else_branch
      
      EVDefault e0 default0 ->
        case evalV fuel' env e0 of
          VVoid -> evalV fuel' env default0
          v -> v
      
      EVVar x -> lookup env x
      
      EVLet x e1 e2 ->
        let v1 = evalV fuel' env e1 in
        evalV fuel' ((x, v1) : env) e2

-- Evaluation with empty environment
evalV_empty :: ExprV -> Value
evalV_empty = evalV 1000 []

-- Example programs (with cleaned up numbers)
simple_let :: ExprV
simple_let =
  EVLet "x" (EVNum 10)
    (EVAdd (EVVar "x") (EVNum 5))

nested_let :: ExprV
nested_let =
  EVLet "x" (EVNum 10)
    (EVLet "y" (EVNum 20)
      (EVAdd (EVVar "x") (EVVar "y")))

complex_with_vars :: ExprV
complex_with_vars =
  EVLet "divisor" (EVNum 0)
    (EVLet "result" (EVDiv (EVNum 100) (EVVar "divisor"))
      (EVDefault (EVVar "result")
        (EVLet "x" (EVNum 10)
          (EVLet "y" (EVNum 32)
            (EVAdd (EVVar "x") (EVVar "y"))))))

-- Thermodynamic types
data VoidInfo = VInfo Prelude.Integer Prelude.Integer VoidSource
  deriving (Prelude.Eq, Prelude.Show)

data VoidSource =
    DivByZero Prelude.Integer
  | ModByZero Prelude.Integer
  | UndefinedVar Prelude.String
  | OutOfFuel
  | TypeError Prelude.String
  | VoidPropagation VoidInfo VoidInfo
  deriving (Prelude.Eq, Prelude.Show)

data ValueT =
    VTNum Prelude.Integer
  | VTBool Prelude.Bool
  | VTVoid VoidInfo
  deriving (Prelude.Eq, Prelude.Show)

-- Universe state
data Universe = Build_Universe {
    total_entropy :: Prelude.Integer,
    time_step :: Prelude.Integer,
    void_count :: Prelude.Integer
  } deriving (Prelude.Eq, Prelude.Show)

-- Initial universe (big bang)
initial_universe :: Universe
initial_universe = Build_Universe 0 0 0

-- Universe evolution
evolve_universe :: Universe -> VoidInfo -> Universe
evolve_universe u (VInfo entropy _ _) =
  Build_Universe {
    total_entropy = total_entropy u Prelude.+ entropy,
    time_step = time_step u Prelude.+ 1,
    void_count = void_count u Prelude.+ 1
  }

-- Combine two voids (entropy accumulates)
combine_voids :: VoidInfo -> VoidInfo -> Universe -> VoidInfo
combine_voids v1@(VInfo e1 t1 s1) v2@(VInfo e2 t2 s2) u =
  VInfo (e1 Prelude.+ e2) (time_step u) (VoidPropagation v1 v2)

-- Lookup for thermodynamic evaluation
lookupT :: [(Prelude.String, ValueT)] -> Prelude.String -> Option ValueT
lookupT [] x = None
lookupT ((y, v) : rest) x =
  if x Prelude.== y
  then Some v
  else lookupT rest x

-- Thermodynamic evaluation
evalT :: Prelude.Integer -> Universe -> [(Prelude.String, ValueT)] -> ExprV -> (ValueT, Universe)
evalT fuel u env e =
  if fuel Prelude.== 0
  then 
    let info = VInfo 1 (time_step u) OutOfFuel in
    (VTVoid info, evolve_universe u info)
  else
    let fuel' = fuel Prelude.- 1 in
    case e of
      EVNum n -> (VTNum n, u)
      
      EVVoid -> 
        let info = VInfo 1 (time_step u) (TypeError "pure_void") in
        (VTVoid info, evolve_universe u info)
      
      EVBool b -> (VTBool b, u)
      
      EVAdd e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum n2) -> (VTNum (n1 Prelude.+ n2), u2)
          (VTNum _, VTVoid i2) -> (VTVoid i2, u2)
          (VTVoid i1, VTNum _) -> (VTVoid i1, u2)
          (VTVoid i1, VTVoid i2) ->
            let combined = combine_voids i1 i2 u2 in
            (VTVoid combined, evolve_universe u2 combined)
          _ -> 
            let info = VInfo 1 (time_step u2) (TypeError "add") in
            (VTVoid info, evolve_universe u2 info)
      
      EVSub e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum n2) -> (VTNum (Prelude.max 0 (n1 Prelude.- n2)), u2)
          (VTNum _, VTVoid i2) -> (VTVoid i2, u2)
          (VTVoid i1, VTNum _) -> (VTVoid i1, u2)
          (VTVoid i1, VTVoid i2) ->
            let combined = combine_voids i1 i2 u2 in
            (VTVoid combined, evolve_universe u2 combined)
          _ -> 
            let info = VInfo 1 (time_step u2) (TypeError "sub") in
            (VTVoid info, evolve_universe u2 info)
      
      EVMul e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum n2) -> (VTNum (n1 Prelude.* n2), u2)
          (VTNum _, VTVoid i2) -> (VTVoid i2, u2)
          (VTVoid i1, VTNum _) -> (VTVoid i1, u2)
          (VTVoid i1, VTVoid i2) ->
            let combined = combine_voids i1 i2 u2 in
            (VTVoid combined, evolve_universe u2 combined)
          _ -> 
            let info = VInfo 1 (time_step u2) (TypeError "mul") in
            (VTVoid info, evolve_universe u2 info)
      
      EVDiv e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum 0) ->
            let info = VInfo 1 (time_step u2) (DivByZero n1) in
            (VTVoid info, evolve_universe u2 info)
          (VTNum n1, VTNum n2) -> (VTNum (n1 `Prelude.div` n2), u2)
          (VTVoid i, _) -> (VTVoid i, u2)
          (_, VTVoid i) -> (VTVoid i, u2)
          _ -> 
            let info = VInfo 1 (time_step u2) (TypeError "div") in
            (VTVoid info, evolve_universe u2 info)
      
      EVMod e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum 0) ->
            let info = VInfo 1 (time_step u2) (ModByZero n1) in
            (VTVoid info, evolve_universe u2 info)
          (VTNum n1, VTNum n2) -> (VTNum (n1 `Prelude.mod` n2), u2)
          (VTVoid i, _) -> (VTVoid i, u2)
          (_, VTVoid i) -> (VTVoid i, u2)
          _ -> 
            let info = VInfo 1 (time_step u2) (TypeError "mod") in
            (VTVoid info, evolve_universe u2 info)
      
      EVIsVoid e0 ->
        let (v, u') = evalT fuel' u env e0 in
        case v of
          VTVoid _ -> (VTBool Prelude.True, u')
          _ -> (VTBool Prelude.False, u')
      
      EVIfVoid cond then_branch else_branch ->
        let (v, u1) = evalT fuel' u env cond in
        case v of
          VTVoid _ -> evalT fuel' u1 env then_branch
          _ -> evalT fuel' u1 env else_branch
      
      EVDefault e0 default0 ->
        let (v, u1) = evalT fuel' u env e0 in
        case v of
          VTVoid _ -> evalT fuel' u1 env default0
          _ -> (v, u1)
      
      EVVar x ->
        case lookupT env x of
          Some v -> (v, u)
          None ->
            let info = VInfo 1 (time_step u) (UndefinedVar x) in
            (VTVoid info, evolve_universe u info)
      
      EVLet x e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1 in
        evalT fuel' u1 ((x, v1) : env) e2

evalT_initial :: ExprV -> (ValueT, Universe)
evalT_initial e = evalT 1000 initial_universe [] e


-- Helper functions
value_entropy :: ValueT -> Prelude.Integer
value_entropy (VTVoid (VInfo e _ _)) = e
value_entropy _ = 0

is_heat_death :: Universe -> Prelude.Bool
is_heat_death u = total_entropy u Prelude.>= 100

-- Example programs from Core module
safe_div :: Prelude.Integer -> Prelude.Integer -> Expr
safe_div n m = EDefault (EDiv (ENum n) (ENum m)) (ENum 0)

divides :: Prelude.Integer -> Prelude.Integer -> Expr
divides n m = EIsVoid (EMod (ENum m) (ENum n))

calculation :: Expr
calculation = EAdd (EDiv (ENum 10) (ENum 2)) (EDiv (ENum 8) (ENum 4))

-- Demo programs
demo_division_chain :: ExprV
demo_division_chain =
  EVLet "x" (EVDiv (EVNum 100) (EVNum 10))
    (EVLet "y" (EVDiv (EVNum 50) (EVNum 0))
      (EVDefault (EVAdd (EVVar "x") (EVVar "y")) (EVNum 999)))

demo_undefined :: ExprV
demo_undefined =
  EVDefault (EVAdd (EVVar "undefined") (EVNum 42))
    (EVMul (EVNum 6) (EVNum 7))

demo_entropy :: ExprV
demo_entropy =
  EVLet "a" (EVDiv (EVNum 1) (EVNum 0))
    (EVLet "b" (EVVar "undefined_var")
      (EVLet "c" (EVMod (EVNum 10) (EVNum 0))
        (EVAdd (EVAdd (EVVar "a") (EVVar "b")) (EVVar "c"))))

demo_recovery :: ExprV
demo_recovery =
  EVDefault
    (EVDefault
      (EVDefault (EVDiv (EVNum 10) (EVNum 0)) (EVNum 1))
      (EVNum 2))
    (EVNum 3)

demo_void_check :: ExprV
demo_void_check =
  EVIfVoid (EVDiv (EVNum 10) (EVNum 0))
    (EVNum 1)
    (EVNum 0)

-- Chaos generator
chaos_generator :: Prelude.Integer -> ExprV
chaos_generator n =
  if n Prelude.== 0
  then EVNum 42
  else EVAdd (EVDiv (EVNum 1) (EVNum 0)) (chaos_generator (n Prelude.- 1))

-- Runner functions
run_basic :: ExprV -> Value
run_basic e = evalV 1000 [] e

run_thermo :: ExprV -> (ValueT, Universe)
run_thermo e = evalT 1000 initial_universe [] e

-- Test programs list
test_programs :: [ExprV]
test_programs =
  [ demo_division_chain
  , demo_undefined
  , demo_entropy
  , demo_recovery
  , demo_void_check
  , simple_let
  , nested_let
  , complex_with_vars
  , chaos_generator 5
  , chaos_generator 10
  ]