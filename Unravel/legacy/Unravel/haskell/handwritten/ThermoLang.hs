module ThermoLang where

import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/))
import Data.Map (Map)
import qualified Data.Map as Map

-- ==========================================
-- 1. THE AST (Abstract Syntax Tree)
-- ==========================================
data Term 
    = Val Int
    | Var String
    | Add Term Term
    | Div Term Term 
    | Let String Term Term
    | Repeat Int Term 
    | Shield Term Term 
    deriving (Show, Eq)

-- ==========================================
-- 2. THE STATIC ANALYZER (The "Compiler")
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

analyze :: Term -> ProgramStats
analyze term = case term of
    Val _ -> mempty
    Var _ -> mempty 
    
    Add t1 t2 -> 
        let s1 = analyze t1
            s2 = analyze t2
            base = ProgramStats 0 1 True
        in s1 <> s2 <> base
        
    Div t1 t2 -> 
        let s1 = analyze t1
            s2 = analyze t2
            base = ProgramStats 1 1 False
        in s1 <> s2 <> base

    Let _ val body -> 
        let sVal = analyze val
            sBody = analyze body
            base = ProgramStats 0 1 True
        in sVal <> sBody <> base

    Repeat n body -> 
        let sBody = analyze body
        in ProgramStats 
            (n Prelude.* maxEntropy sBody) 
            (n Prelude.* timeCost sBody) 
            (isSafe sBody)

    Shield try fallback -> 
        let sTry = analyze try
            sFallback = analyze fallback
        in sTry <> sFallback

-- ==========================================
-- 3. THE COMPILER TARGET (Transpiler)
-- ==========================================

compile :: Term -> Map String Int -> Unravel Int
compile term env = case term of
    Val n -> return n
    
    Var s -> case Map.lookup s env of
        Just v  -> return v
        Nothing -> crumble (LogicError $ "Variable not found: " ++ s)

    Add t1 t2 -> do
        v1 <- compile t1 env
        v2 <- compile t2 env
        return (v1 Prelude.+ v2)

    Div t1 t2 -> do
        v1 <- compile t1 env
        v2 <- compile t2 env
        uDiv v1 v2

    Let name val body -> do
        v <- compile val env
        compile body (Map.insert name v env)

    Repeat n body -> 
        if n Prelude.<= 0 then return 0
        else do
            _ <- compile body env 
            compile (Repeat (n Prelude.- 1) body) env

    Shield try fallback -> 
        let computation = compile try env
        in recover computation 0 

-- ==========================================
-- 4. THE TOTALITY ENGINE
-- ==========================================

data CompilationResult 
    = Accepted ProgramStats (Unravel Int)
    | Rejected String

-- MANUAL SHOW INSTANCE (The Fix)
-- We print the stats, but hide the function execution behind a placeholder
instance Show CompilationResult where
    show (Accepted stats _) = "Accepted " ++ show stats ++ " <Executable>"
    show (Rejected reason)  = "Rejected: " ++ reason

build :: Term -> CompilationResult
build term = 
    let stats = analyze term
    in if timeCost stats Prelude.> 10000 
       then Rejected "Program exceeds Time Budget (Halting Guarantee enforced)"
       else Accepted stats (compile term Map.empty)