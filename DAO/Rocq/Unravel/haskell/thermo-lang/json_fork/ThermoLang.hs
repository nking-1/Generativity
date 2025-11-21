module ThermoLang where

import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/), id)
import Data.Map (Map)
import qualified Data.Map as Map

-- ==========================================
-- 1. AST
-- ==========================================
data Term 
    = IntVal Int
    | BoolVal Bool
    | StrVal String     -- NEW
    | ListVal [Term]
    | Var String
    
    | Add Term Term
    | Div Term Term 
    | Eq Term Term
    | If Term Term Term
    | Let String Term Term
    | Map String Term Term
    | Fold String String Term Term Term
    | Repeat Int Term 
    | Shield Term Term 
    | Log String Term
    
    | Get String Term   -- NEW: obj.field
    deriving (Show, Eq)

-- ==========================================
-- 2. VALUES
-- ==========================================
data UVal 
    = VInt Int
    | VBool Bool
    | VString String            -- NEW
    | VList [UVal]
    | VObject (Map String UVal) -- NEW: JSON Object
    deriving (Show, Eq)

-- Helpers
asInt :: UVal -> Unravel Int
asInt (VInt i) = return i
asInt _        = crumble (LogicError "Expected Int")

asBool :: UVal -> Unravel Bool
asBool (VBool b) = return b
asBool _         = crumble (LogicError "Expected Bool")

asList :: UVal -> Unravel [UVal]
asList (VList l) = return l
asList _         = crumble (LogicError "Expected List")

asObj :: UVal -> Unravel (Map String UVal)
asObj (VObject m) = return m
asObj _           = crumble (LogicError "Expected Object")

-- ==========================================
-- 3. ANALYZER
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

type AnalysisContext = Map String Int

analyze :: Term -> AnalysisContext -> ProgramStats
analyze term ctx = case term of
    IntVal _  -> mempty
    BoolVal _ -> mempty
    StrVal _  -> mempty
    Var _     -> mempty
    
    ListVal xs -> Prelude.foldMap (\t -> analyze t ctx) xs

    Add t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True
    Div t1 t2 -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 1 1 False
    Eq t1 t2  -> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True

    If cond t1 t2 -> 
        analyze cond ctx <> analyze t1 ctx <> analyze t2 ctx <> ProgramStats 0 1 True

    Let name val body -> 
        analyze val ctx <> analyze body (Map.insert name 1 ctx)

    Map var body listTerm -> 
        let sList = analyze listTerm ctx
            sBody = analyze body (Map.insert var 1 ctx)
        in sList <> ProgramStats 
            (100 Prelude.* maxEntropy sBody) 
            (100 Prelude.* timeCost sBody) 
            (isSafe sBody)

    Fold acc var body initTerm listTerm ->
        let sInit = analyze initTerm ctx
            sList = analyze listTerm ctx
            sBody = analyze body (Map.insert var 1 (Map.insert acc 1 ctx))
        in sInit <> sList <> ProgramStats 
            (100 Prelude.* maxEntropy sBody) 
            (100 Prelude.* timeCost sBody) 
            (isSafe sBody)

    Repeat n body -> 
        let sBody = analyze body ctx
        in ProgramStats (n Prelude.* maxEntropy sBody) (n Prelude.* timeCost sBody) (isSafe sBody)

    Shield try fallback -> 
        analyze try ctx <> analyze fallback ctx
        
    Log _ t -> analyze t ctx
    
    -- Accessing a field is risky (might not exist)
    Get _ t -> analyze t ctx <> ProgramStats 1 1 False

-- ==========================================
-- 4. COMPILER
-- ==========================================

compile :: Term -> Map String UVal -> Unravel UVal
compile term env = case term of
    IntVal i  -> return (VInt i)
    BoolVal b -> return (VBool b)
    StrVal s  -> return (VString s)
    ListVal l -> VList Prelude.<$> Prelude.mapM (\t -> compile t env) l
    
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
        res <- uDiv v1 v2 
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
            backup      = compile fallback env >>= \b -> return b 
        in do
            def <- backup
            recover computation def

    Log msg term -> do
        v <- compile term env
        return v
        
    Get field objTerm -> do
        obj <- compile objTerm env >>= asObj
        case Map.lookup field obj of
            Just v  -> return v
            Nothing -> crumble (JsonError $ "Field not found: " ++ field)

-- ==========================================
-- 5. BUILDER
-- ==========================================

data CompilationResult 
    = Accepted ProgramStats (Unravel UVal)
    | Rejected String

instance Show CompilationResult where
    show (Accepted stats _) = "Accepted " ++ show stats
    show (Rejected reason)  = "Rejected: " ++ reason

build :: Term -> CompilationResult
build term = 
    let stats = analyze term Map.empty
    in if timeCost stats Prelude.> 20000 
       then Rejected "Time Budget Exceeded"
       else Accepted stats (compile term Map.empty)