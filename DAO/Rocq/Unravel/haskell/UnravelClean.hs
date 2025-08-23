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