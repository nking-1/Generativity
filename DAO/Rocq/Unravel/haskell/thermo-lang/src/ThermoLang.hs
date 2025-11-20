module ThermoLang where

import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/), id)
import Data.Map (Map)
import qualified Data.Map as Map

-- ==========================================
-- 1. THE AST (Now with Data & Logic)
-- ==========================================
data Term 
    -- Primitives
    = IntVal Int
    | BoolVal Bool
    | ListVal [Term]    -- Recursive definition for literals
    | Var String
    
    -- Arithmetic
    | Add Term Term
    | Div Term Term 
    
    -- Logic
    | Eq Term Term
    | If Term Term Term
    
    -- Binding
    | Let String Term Term
    
    -- Data Processing
    | Map String Term Term  -- Map (var -> body) list
    | Fold String String Term Term Term -- Fold (acc -> var -> body) init list
    
    -- Control / Error
    | Repeat Int Term 
    | Shield Term Term 
    | Log String Term
    deriving (Show, Eq)

-- ==========================================
-- 2. RUNTIME VALUES (The Type System)
-- ==========================================
data UVal 
    = VInt Int
    | VBool Bool
    | VList [UVal]
    deriving (Show, Eq)

-- Helpers to extract values (Runtime Type Checking)
-- If types don't match, it generates Entropy (LogicError)
asInt :: UVal -> Unravel Int
asInt (VInt i) = return i
asInt _        = crumble (LogicError "Type Mismatch: Expected Int")

asBool :: UVal -> Unravel Bool
asBool (VBool b) = return b
asBool _         = crumble (LogicError "Type Mismatch: Expected Bool")

asList :: UVal -> Unravel [UVal]
asList (VList l) = return l
asList _         = crumble (LogicError "Type Mismatch: Expected List")

-- ==========================================
-- 3. THE STATIC ANALYZER
-- ==========================================

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

-- We pass a context to track list lengths for cost estimation
type AnalysisContext = Map String Int

analyze :: Term -> AnalysisContext -> ProgramStats
analyze term ctx = case term of
    IntVal _  -> mempty
    BoolVal _ -> mempty
    Var _     -> mempty
    
    ListVal xs -> 
        Prelude.foldMap (\t -> analyze t ctx) xs

    Add t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True
    
    -- Worst case entropy assumption for Div
    Div t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 1 1 False
    
    Eq t1 t2  -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True

    If cond t1 t2 -> 
        let sC = analyze cond ctx
            s1 = analyze t1 ctx
            s2 = analyze t2 ctx
            -- Branching cost: sum of branches (conservative) or max?
            -- Conservative: Sum them (we might execute parts speculatively in Applicative)
            -- Or Max. Let's use Sum for safety.
        in sC <> s1 <> s2 <> ProgramStats 0 1 True

    Let name val body -> 
        let sVal  = analyze val ctx
            -- Simple heuristic: If it's a list, we track length 1 (abstract)
            -- In a real compiler, we'd do constant propagation
            ctx'  = Map.insert name 1 ctx 
            sBody = analyze body ctx'
        in sVal <> sBody

    -- Map: Cost = ListLength * Cost(Body)
    -- We assume standard batch size 100 if unknown
    Map var body listTerm -> 
        let sList = analyze listTerm ctx
            sBody = analyze body (Map.insert var 1 ctx)
            batchSize = 100 
        in sList <> ProgramStats 
            (batchSize Prelude.* maxEntropy sBody) 
            (batchSize Prelude.* timeCost sBody) 
            (isSafe sBody)

    -- Fold: Same as Map
    Fold acc var body init listTerm ->
        let sInit = analyze init ctx
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

-- ==========================================
-- 4. THE COMPILER (Transpiler)
-- ==========================================

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
        v1 <- compile t1 env >>= asInt
        v2 <- compile t2 env >>= asInt
        return (VInt (v1 Prelude.+ v2))

    Div t1 t2 -> do
        v1 <- compile t1 env >>= asInt
        v2 <- compile t2 env >>= asInt
        res <- uDiv v1 v2 -- Returns Unravel Int
        return (VInt res)

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
    
    -- The Harvester Implementation
    Map var body listTerm -> do
        listVals <- compile listTerm env >>= asList
        
        -- We create a list of Unravel computations
        let ops = Prelude.map (\val -> compile body (Map.insert var val env)) listVals
        
        -- Run the Harvest
        results <- harvest ops
        return (VList results)

    -- The Folding Harvester
    Fold accName varName body initTerm listTerm -> do
        initVal  <- compile initTerm env
        listVals <- compile listTerm env >>= asList
        
        -- Monadic Fold
        let folder acc val = compile body (Map.insert varName val (Map.insert accName acc env))
        
        -- We foldM over the list. 
        -- Note: foldM in Unravel naturally accumulates entropy!
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
            backup      = compile fallback env >>= \b -> return b -- strictness
        -- We need to be careful: recover takes a Value, not a computation for default
        -- Simplified for demo: we run fallback first to get the value
        -- In full language, we'd need lazy recovery
        in do
            def <- backup
            recover computation def

    Log msg term -> do
        v <- compile term env
        -- In a real compiler, this would emit IO or write to a specific log
        -- Here we just pass through
        return v

-- ==========================================
-- 5. BUILDER
-- ==========================================

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