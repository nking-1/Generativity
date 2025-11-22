module ThermoLang where

import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/), id)
import Data.Map (Map)
import qualified Data.Map as Map

-- ==========================================
-- 1. THE AST
-- ==========================================
data Term 
    = IntVal Int
    | BoolVal Bool
    | ListVal [Term]
    | Var String
    | Add Term Term
    | Sub Term Term
    | Mul Term Term
    | Div Term Term 
    | Eq Term Term
    | If Term Term Term
    | Let String Term Term
    | Map String Term Term 
    | Fold String String Term Term Term
    | Repeat Int Term 
    | Shield Term Term 
    | Log String Term
    | GetEntropy 
    | GetHologram 
    deriving (Show, Eq)

-- ==========================================
-- 2. RUNTIME VALUES (The Wheel)
-- ==========================================
data UVal 
    = VInt Int
    | VBool Bool
    | VList [UVal]
    | VInf          
    | VNull         
    | VHash Integer 
    deriving (Show, Eq)

-- Helpers
asInt :: UVal -> Unravel Int
asInt (VInt i) = return i
asInt VInf     = crumble (LogicError "Collapsed Infinity to Int")
asInt VNull    = crumble (LogicError "Collapsed Nullity to Int")
asInt _        = crumble (LogicError "Type Mismatch: Expected Int")

asBool :: UVal -> Unravel Bool
asBool (VBool b) = return b
asBool _         = crumble (LogicError "Type Mismatch: Expected Bool")

asList :: UVal -> Unravel [UVal]
asList (VList l) = return l
asList _         = crumble (LogicError "Type Mismatch: Expected List")

-- Wheel Arithmetic
wheelAdd :: UVal -> UVal -> UVal
wheelAdd VNull _ = VNull
wheelAdd _ VNull = VNull
wheelAdd VInf _  = VInf
wheelAdd _ VInf  = VInf
wheelAdd (VInt a) (VInt b) = VInt (a Prelude.+ b)
wheelAdd _ _ = VNull

wheelSub :: UVal -> UVal -> UVal
wheelSub VNull _ = VNull
wheelSub _ VNull = VNull
wheelSub VInf _  = VInf
wheelSub _ VInf  = VInf
wheelSub (VInt a) (VInt b) = VInt (a Prelude.- b)
wheelSub _ _ = VNull

wheelMul :: UVal -> UVal -> UVal
wheelMul VNull _ = VNull
wheelMul _ VNull = VNull
wheelMul (VInt 0) VInf = VNull
wheelMul VInf (VInt 0) = VNull
wheelMul VInf _  = VInf
wheelMul _ VInf  = VInf
wheelMul (VInt a) (VInt b) = VInt (a Prelude.* b)
wheelMul _ _ = VNull

wheelDiv :: UVal -> UVal -> UVal
wheelDiv VNull _ = VNull
wheelDiv _ VNull = VNull
wheelDiv _ VInf  = VInt 0
wheelDiv VInf _  = VInf
wheelDiv (VInt 0) (VInt 0) = VNull
wheelDiv (VInt _) (VInt 0) = VInf
wheelDiv (VInt a) (VInt b) = VInt (a `Prelude.div` b)
wheelDiv _ _ = VNull

-- Static Analysis
data ProgramStats = ProgramStats {
    maxEntropy :: Int,
    timeCost   :: Int,
    isSafe     :: Bool
} deriving (Show)

instance Semigroup ProgramStats where
    (ProgramStats e1 t1 s1) <> (ProgramStats e2 t2 s2) = 
        ProgramStats (e1 Prelude.+ e2) (t1 Prelude.+ t2) (s1 && s2)

instance Monoid ProgramStats where
    mempty = ProgramStats 0 0 True

type AnalysisContext = Map String Int

analyze :: Term -> AnalysisContext -> ProgramStats
analyze term ctx = case term of
    IntVal _  -> mempty
    BoolVal _ -> mempty
    Var _     -> mempty
    GetEntropy -> mempty 
    GetHologram -> mempty
    ListVal xs -> Prelude.foldMap (\t -> analyze t ctx) xs
    Add t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True
    Sub t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True
    Mul t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True
    Div t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True
    Eq t1 t2  -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True
    If cond t1 t2 -> 
        let sC = analyze cond ctx
            s1 = analyze t1 ctx
            s2 = analyze t2 ctx
        in sC <> s1 <> s2 <> ProgramStats 0 1 True
    Let name val body -> 
        let sVal  = analyze val ctx
            ctx'  = Map.insert name 1 ctx 
            sBody = analyze body ctx'
        in sVal <> sBody
    Map var body listTerm -> 
        let sList = analyze listTerm ctx
            sBody = analyze body (Map.insert var 1 ctx)
            batchSize = 100 
        in sList <> ProgramStats 
            (batchSize Prelude.* maxEntropy sBody) 
            (batchSize Prelude.* timeCost sBody) 
            (isSafe sBody)
    Fold acc var body initTerm listTerm ->
        let sInit = analyze initTerm ctx
            sList = analyze listTerm ctx
            sBody = analyze body (Map.insert var 1 (Map.insert acc 1 ctx))
            batchSize = 100
        in sInit <> sList <> ProgramStats 
            (batchSize Prelude.* maxEntropy sBody) 
            (batchSize Prelude.* timeCost sBody) 
            (isSafe sBody)
    Repeat n body -> 
        let sBody = analyze body ctx
        in ProgramStats 
            (n Prelude.* maxEntropy sBody) 
            (n Prelude.* timeCost sBody) 
            (isSafe sBody)
    Shield try fallback -> 
        analyze try ctx <> analyze fallback ctx
    Log _ t -> analyze t ctx

-- Compiler
compile :: Term -> Map String UVal -> Unravel UVal
compile term env = case term of
    IntVal i  -> return (VInt i)
    BoolVal b -> return (VBool b)
    ListVal l -> do
        vs <- Prelude.mapM (\t -> compile t env) l
        return (VList vs)
    Var s -> case Map.lookup s env of
        Just v  -> return v
        Nothing -> crumble (LogicError $ "Var not found: " ++ s)
    Add t1 t2 -> do
        v1 <- compile t1 env
        v2 <- compile t2 env
        return (wheelAdd v1 v2)
    Sub t1 t2 -> do
        v1 <- compile t1 env
        v2 <- compile t2 env
        return (wheelSub v1 v2)
    Mul t1 t2 -> do
        v1 <- compile t1 env
        v2 <- compile t2 env
        return (wheelMul v1 v2)
    Div t1 t2 -> do
        v1 <- compile t1 env
        v2 <- compile t2 env
        return (wheelDiv v1 v2)
    Eq t1 t2 -> do
        v1 <- compile t1 env
        v2 <- compile t2 env
        return (VBool (v1 Prelude.== v2))
    If cond t1 t2 -> do
        b <- compile cond env >>= asBool
        if b then compile t1 env else compile t2 env
    Let name val body -> do
        v <- compile val env
        compile body (Map.insert name v env)
    GetEntropy -> do
        e <- currentEntropy
        return (VInt e)
    GetHologram -> do
        h <- getHologram
        return (VHash h)
    Map var body listTerm -> do
        listVals <- compile listTerm env >>= asList
        let ops = Prelude.map (\val -> compile body (Map.insert var val env)) listVals
        results <- harvest ops
        return (VList results)
    Fold accName varName body initTerm listTerm -> do
        initVal  <- compile initTerm env
        listVals <- compile listTerm env >>= asList
        let folder acc val = compile body (Map.insert varName val (Map.insert accName acc env))
        final <- Prelude.foldl 
                    (\accM val -> do
                        acc <- accM
                        folder acc val
                    ) (return initVal) listVals
        return final
    Repeat n body -> 
        if n Prelude.<= 0 then return (VInt 0)
        else do
            _ <- compile body env 
            compile (Repeat (n Prelude.- 1) body) env
    Shield try fallback -> 
        let computation = compile try env
            backup      = compile fallback env 
        in do
            def <- backup
            let collapsedComputation = Unravel $ \u -> 
                    let (r, u') = runUnravel computation u
                    in case r of
                        Valid val -> case val of
                            VInf  -> runUnravel (crumble (LogicError "Collapsed Infinity")) u'
                            VNull -> runUnravel (crumble (LogicError "Collapsed Nullity")) u'
                            _     -> (Valid val, u')
                        Invalid i -> (Invalid i, u')
            recover collapsedComputation def
    Log _ t -> do
        v <- compile t env
        return v

data CompilationResult 
    = Accepted ProgramStats (Unravel UVal)
    | Rejected String

instance Show CompilationResult where
    show (Accepted stats _) = "Accepted " ++ show stats ++ " <Executable>"
    show (Rejected reason)  = "Rejected: " ++ reason

build :: Term -> CompilationResult
build term = 
    let stats = analyze term Map.empty
    in if timeCost stats Prelude.> 20000 
       then Rejected "Time Budget Exceeded"
       else Accepted stats (compile term Map.empty)