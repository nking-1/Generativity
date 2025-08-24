-- UnravelCleanV2.hs
module UnravelCleanV2 where

import Prelude hiding (lookup)

-- ============================================================
-- CONFIGURATION CONSTANTS
-- ============================================================

-- Default computational fuel (can be overridden)
defaultFuel :: Integer
defaultFuel = 1000

-- Heat death threshold for universe
heatDeathThreshold :: Integer
heatDeathThreshold = 100

-- Base entropy generated per void event
baseEntropy :: Integer
baseEntropy = 1

-- ============================================================
-- CORE TYPES
-- ============================================================

-- Option type (Maybe in standard Haskell)
data Option a = Some a | None
  deriving (Eq, Show)

-- ============================================================
-- BASIC EXPRESSION LANGUAGE
-- ============================================================

-- Expression type (no variables)
data Expr = 
    ENum Integer
  | EVoid
  | EBool Bool
  | EAdd Expr Expr
  | ESub Expr Expr
  | EMul Expr Expr
  | EDiv Expr Expr
  | EMod Expr Expr
  | EIsVoid Expr
  | EIfVoid Expr Expr Expr
  | EDefault Expr Expr
  deriving (Eq, Show)

-- Value type
data Value =
    VNum Integer
  | VBool Bool
  | VVoid
  deriving (Eq, Show)

-- ============================================================
-- BASIC EVALUATION
-- ============================================================

-- Core evaluation with fuel
eval :: Integer -> Expr -> Value
eval fuel e =
  if fuel == 0 
  then VVoid
  else 
    let fuel' = fuel - 1 in
    case e of
      ENum n -> VNum n
      EVoid -> VVoid
      EBool b -> VBool b
      
      EAdd e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum n2) -> VNum (n1 + n2)
          _ -> VVoid
      
      ESub e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum n2) -> VNum (max 0 (n1 - n2))  -- Saturating
          _ -> VVoid
      
      EMul e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum n2) -> VNum (n1 * n2)
          _ -> VVoid
      
      EDiv e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum 0) -> VVoid
          (VNum n1, VNum n2) -> VNum (n1 `div` n2)
          _ -> VVoid
      
      EMod e1 e2 ->
        case (eval fuel' e1, eval fuel' e2) of
          (VNum n1, VNum 0) -> VVoid
          (VNum n1, VNum n2) -> VNum (n1 `mod` n2)
          _ -> VVoid
      
      EIsVoid e0 ->
        case eval fuel' e0 of
          VVoid -> VBool True
          _ -> VBool False
      
      EIfVoid cond thenBranch elseBranch ->
        case eval fuel' cond of
          VVoid -> eval fuel' thenBranch
          _ -> eval fuel' elseBranch
      
      EDefault e0 defaultVal ->
        case eval fuel' e0 of
          VVoid -> eval fuel' defaultVal
          v -> v

-- Evaluation with default fuel
evalDefault :: Expr -> Value
evalDefault = eval defaultFuel

-- Evaluation with custom fuel
evalWithFuel :: Integer -> Expr -> Value
evalWithFuel = eval

-- ============================================================
-- EXPRESSION LANGUAGE WITH VARIABLES
-- ============================================================

-- Expression with variables
data ExprV =
    EVNum Integer
  | EVVoid
  | EVBool Bool
  | EVAdd ExprV ExprV
  | EVSub ExprV ExprV
  | EVMul ExprV ExprV
  | EVDiv ExprV ExprV
  | EVMod ExprV ExprV
  | EVIsVoid ExprV
  | EVIfVoid ExprV ExprV ExprV
  | EVDefault ExprV ExprV
  | EVVar String
  | EVLet String ExprV ExprV
  deriving (Eq, Show)

-- Environment type
type Env = [(String, Value)]

-- Lookup variable in environment
lookup :: Env -> String -> Value
lookup [] _ = VVoid
lookup ((y, v) : rest) x =
  if x == y then v else lookup rest x

-- Evaluation with environment and fuel
evalV :: Integer -> Env -> ExprV -> Value
evalV fuel env e =
  if fuel == 0
  then VVoid
  else
    let fuel' = fuel - 1 in
    case e of
      EVNum n -> VNum n
      EVVoid -> VVoid
      EVBool b -> VBool b
      
      EVAdd e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum n2) -> VNum (n1 + n2)
          _ -> VVoid
      
      EVSub e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum n2) -> VNum (max 0 (n1 - n2))
          _ -> VVoid
      
      EVMul e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum n2) -> VNum (n1 * n2)
          _ -> VVoid
      
      EVDiv e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum 0) -> VVoid
          (VNum n1, VNum n2) -> VNum (n1 `div` n2)
          _ -> VVoid
      
      EVMod e1 e2 ->
        case (evalV fuel' env e1, evalV fuel' env e2) of
          (VNum n1, VNum 0) -> VVoid
          (VNum n1, VNum n2) -> VNum (n1 `mod` n2)
          _ -> VVoid
      
      EVIsVoid e0 ->
        case evalV fuel' env e0 of
          VVoid -> VBool True
          _ -> VBool False
      
      EVIfVoid cond thenBranch elseBranch ->
        case evalV fuel' env cond of
          VVoid -> evalV fuel' env thenBranch
          _ -> evalV fuel' env elseBranch
      
      EVDefault e0 defaultVal ->
        case evalV fuel' env e0 of
          VVoid -> evalV fuel' env defaultVal
          v -> v
      
      EVVar x -> lookup env x
      
      EVLet x e1 e2 ->
        let v1 = evalV fuel' env e1 in
        evalV fuel' ((x, v1) : env) e2

-- Convenient evaluation functions
evalVEmpty :: ExprV -> Value
evalVEmpty = evalV defaultFuel []

evalVWithFuel :: Integer -> ExprV -> Value
evalVWithFuel fuel = evalV fuel []

evalVWithEnv :: Env -> ExprV -> Value
evalVWithEnv = evalV defaultFuel

evalVFull :: Integer -> Env -> ExprV -> Value
evalVFull = evalV

-- ============================================================
-- THERMODYNAMIC LAYER
-- ============================================================

-- Void information (entropy tracking)
data VoidInfo = VInfo {
    entropy :: Integer,
    timeCreated :: Integer,
    source :: VoidSource
  } deriving (Eq, Show)

-- Sources of void (entropy generators)
data VoidSource =
    DivByZero Integer
  | ModByZero Integer
  | UndefinedVar String
  | OutOfFuel
  | TypeError String
  | VoidPropagation VoidInfo VoidInfo
  deriving (Eq, Show)

-- Thermodynamic value
data ValueT =
    VTNum Integer
  | VTBool Bool
  | VTVoid VoidInfo
  deriving (Eq, Show)

-- Universe state
data Universe = Universe {
    totalEntropy :: Integer,
    timeStep :: Integer,
    voidCount :: Integer
  } deriving (Eq, Show)

-- ============================================================
-- UNIVERSE OPERATIONS
-- ============================================================

-- Initial universe (big bang)
initialUniverse :: Universe
initialUniverse = Universe 0 0 0

-- Create void information
makeVoidInfo :: Integer -> Universe -> VoidSource -> VoidInfo
makeVoidInfo entropyAmount u src = 
  VInfo entropyAmount (timeStep u) src

-- Evolve universe when void occurs
evolveUniverse :: Universe -> VoidInfo -> Universe
evolveUniverse u (VInfo entropyAmount _ _) =
  Universe {
    totalEntropy = totalEntropy u + entropyAmount,
    timeStep = timeStep u + 1,
    voidCount = voidCount u + 1
  }

-- Combine two voids (entropy accumulates)
combineVoids :: VoidInfo -> VoidInfo -> Universe -> VoidInfo
combineVoids v1@(VInfo e1 _ _) v2@(VInfo e2 _ _) u =
  VInfo (e1 + e2) (timeStep u) (VoidPropagation v1 v2)

-- Check for heat death
isHeatDeath :: Universe -> Bool
isHeatDeath u = totalEntropy u >= heatDeathThreshold

isHeatDeathCustom :: Integer -> Universe -> Bool
isHeatDeathCustom threshold u = totalEntropy u >= threshold

-- Get entropy from thermodynamic value
valueEntropy :: ValueT -> Integer
valueEntropy (VTVoid (VInfo e _ _)) = e
valueEntropy _ = 0

-- ============================================================
-- THERMODYNAMIC ENVIRONMENT
-- ============================================================

type EnvT = [(String, ValueT)]

-- Lookup for thermodynamic evaluation
lookupT :: EnvT -> String -> Option ValueT
lookupT [] _ = None
lookupT ((y, v) : rest) x =
  if x == y then Some v else lookupT rest x

-- ============================================================
-- THERMODYNAMIC EVALUATION
-- ============================================================

-- Main thermodynamic evaluator
evalT :: Integer -> Universe -> EnvT -> ExprV -> (ValueT, Universe)
evalT fuel u env e =
  if fuel == 0
  then 
    let info = makeVoidInfo baseEntropy u OutOfFuel in
    (VTVoid info, evolveUniverse u info)
  else
    let fuel' = fuel - 1 in
    case e of
      EVNum n -> (VTNum n, u)
      
      EVVoid -> 
        let info = makeVoidInfo baseEntropy u (TypeError "pure_void") in
        (VTVoid info, evolveUniverse u info)
      
      EVBool b -> (VTBool b, u)
      
      EVAdd e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum n2) -> (VTNum (n1 + n2), u2)
          (VTNum _, VTVoid i2) -> (VTVoid i2, u2)
          (VTVoid i1, VTNum _) -> (VTVoid i1, u2)
          (VTVoid i1, VTVoid i2) ->
            let combined = combineVoids i1 i2 u2 in
            (VTVoid combined, evolveUniverse u2 combined)
          _ -> 
            let info = makeVoidInfo baseEntropy u2 (TypeError "add") in
            (VTVoid info, evolveUniverse u2 info)
      
      EVSub e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum n2) -> (VTNum (max 0 (n1 - n2)), u2)
          (VTNum _, VTVoid i2) -> (VTVoid i2, u2)
          (VTVoid i1, VTNum _) -> (VTVoid i1, u2)
          (VTVoid i1, VTVoid i2) ->
            let combined = combineVoids i1 i2 u2 in
            (VTVoid combined, evolveUniverse u2 combined)
          _ -> 
            let info = makeVoidInfo baseEntropy u2 (TypeError "sub") in
            (VTVoid info, evolveUniverse u2 info)
      
      EVMul e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum n2) -> (VTNum (n1 * n2), u2)
          (VTNum _, VTVoid i2) -> (VTVoid i2, u2)
          (VTVoid i1, VTNum _) -> (VTVoid i1, u2)
          (VTVoid i1, VTVoid i2) ->
            let combined = combineVoids i1 i2 u2 in
            (VTVoid combined, evolveUniverse u2 combined)
          _ -> 
            let info = makeVoidInfo baseEntropy u2 (TypeError "mul") in
            (VTVoid info, evolveUniverse u2 info)
      
      EVDiv e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum 0) ->
            let info = makeVoidInfo baseEntropy u2 (DivByZero n1) in
            (VTVoid info, evolveUniverse u2 info)
          (VTNum n1, VTNum n2) -> (VTNum (n1 `div` n2), u2)
          (VTVoid i, _) -> (VTVoid i, u2)
          (_, VTVoid i) -> (VTVoid i, u2)
          _ -> 
            let info = makeVoidInfo baseEntropy u2 (TypeError "div") in
            (VTVoid info, evolveUniverse u2 info)
      
      EVMod e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1
            (v2, u2) = evalT fuel' u1 env e2
        in case (v1, v2) of
          (VTNum n1, VTNum 0) ->
            let info = makeVoidInfo baseEntropy u2 (ModByZero n1) in
            (VTVoid info, evolveUniverse u2 info)
          (VTNum n1, VTNum n2) -> (VTNum (n1 `mod` n2), u2)
          (VTVoid i, _) -> (VTVoid i, u2)
          (_, VTVoid i) -> (VTVoid i, u2)
          _ -> 
            let info = makeVoidInfo baseEntropy u2 (TypeError "mod") in
            (VTVoid info, evolveUniverse u2 info)
      
      EVIsVoid e0 ->
        let (v, u') = evalT fuel' u env e0 in
        case v of
          VTVoid _ -> (VTBool True, u')
          _ -> (VTBool False, u')
      
      EVIfVoid cond thenBranch elseBranch ->
        let (v, u1) = evalT fuel' u env cond in
        case v of
          VTVoid _ -> evalT fuel' u1 env thenBranch
          _ -> evalT fuel' u1 env elseBranch
      
      EVDefault e0 defaultVal ->
        let (v, u1) = evalT fuel' u env e0 in
        case v of
          VTVoid _ -> evalT fuel' u1 env defaultVal
          _ -> (v, u1)
      
      EVVar x ->
        case lookupT env x of
          Some v -> (v, u)
          None ->
            let info = makeVoidInfo baseEntropy u (UndefinedVar x) in
            (VTVoid info, evolveUniverse u info)
      
      EVLet x e1 e2 ->
        let (v1, u1) = evalT fuel' u env e1 in
        evalT fuel' u1 ((x, v1) : env) e2

-- Convenient thermodynamic evaluation functions
evalTInitial :: ExprV -> (ValueT, Universe)
evalTInitial = evalT defaultFuel initialUniverse []

evalTWithFuel :: Integer -> ExprV -> (ValueT, Universe)
evalTWithFuel fuel = evalT fuel initialUniverse []

evalTWithUniverse :: Universe -> ExprV -> (ValueT, Universe)
evalTWithUniverse u = evalT defaultFuel u []

evalTFull :: Integer -> Universe -> EnvT -> ExprV -> (ValueT, Universe)
evalTFull = evalT

-- ============================================================
-- RUNNER FUNCTIONS (for compatibility)
-- ============================================================

runBasic :: ExprV -> Value
runBasic = evalVEmpty

runBasicWithFuel :: Integer -> ExprV -> Value
runBasicWithFuel = evalVWithFuel

runThermo :: ExprV -> (ValueT, Universe)
runThermo = evalTInitial

runThermoWithFuel :: Integer -> ExprV -> (ValueT, Universe)
runThermoWithFuel = evalTWithFuel

-- ============================================================
-- EXAMPLE PROGRAMS
-- ============================================================

simpleLet :: ExprV
simpleLet = EVLet "x" (EVNum 10) (EVAdd (EVVar "x") (EVNum 5))

nestedLet :: ExprV
nestedLet = 
  EVLet "x" (EVNum 10)
    (EVLet "y" (EVNum 20)
      (EVAdd (EVVar "x") (EVVar "y")))

complexWithVars :: ExprV
complexWithVars =
  EVLet "divisor" (EVNum 0)
    (EVLet "result" (EVDiv (EVNum 100) (EVVar "divisor"))
      (EVDefault (EVVar "result")
        (EVLet "x" (EVNum 10)
          (EVLet "y" (EVNum 32)
            (EVAdd (EVVar "x") (EVVar "y"))))))

-- Demo programs
demoDivisionChain :: ExprV
demoDivisionChain =
  EVLet "x" (EVDiv (EVNum 100) (EVNum 10))
    (EVLet "y" (EVDiv (EVNum 50) (EVNum 0))
      (EVDefault (EVAdd (EVVar "x") (EVVar "y")) (EVNum 999)))

demoUndefined :: ExprV
demoUndefined =
  EVDefault (EVAdd (EVVar "undefined") (EVNum 42))
    (EVMul (EVNum 6) (EVNum 7))

demoEntropy :: ExprV
demoEntropy =
  EVLet "a" (EVDiv (EVNum 1) (EVNum 0))
    (EVLet "b" (EVVar "undefined_var")
      (EVLet "c" (EVMod (EVNum 10) (EVNum 0))
        (EVAdd (EVAdd (EVVar "a") (EVVar "b")) (EVVar "c"))))

demoRecovery :: ExprV
demoRecovery =
  EVDefault
    (EVDefault
      (EVDefault (EVDiv (EVNum 10) (EVNum 0)) (EVNum 1))
      (EVNum 2))
    (EVNum 3)

demoVoidCheck :: ExprV
demoVoidCheck =
  EVIfVoid (EVDiv (EVNum 10) (EVNum 0))
    (EVNum 1)
    (EVNum 0)

-- Chaos generator
chaosGenerator :: Integer -> ExprV
chaosGenerator n =
  if n == 0
  then EVNum 42
  else EVAdd (EVDiv (EVNum 1) (EVNum 0)) (chaosGenerator (n - 1))

-- Test programs list
testPrograms :: [ExprV]
testPrograms =
  [ demoDivisionChain
  , demoUndefined
  , demoEntropy
  , demoRecovery
  , demoVoidCheck
  , simpleLet
  , nestedLet
  , complexWithVars
  , chaosGenerator 5
  , chaosGenerator 10
  ]

-- ============================================================
-- HELPER FUNCTIONS
-- ============================================================

safeDivExpr :: Integer -> Integer -> Expr
safeDivExpr n m = EDefault (EDiv (ENum n) (ENum m)) (ENum 0)

dividesExpr :: Integer -> Integer -> Expr
dividesExpr n m = EIsVoid (EMod (ENum m) (ENum n))

calculationExpr :: Expr
calculationExpr = EAdd (EDiv (ENum 10) (ENum 2)) (EDiv (ENum 8) (ENum 4))