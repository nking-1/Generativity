module ThermoTypeSystem where

import ThermoLangV2
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (foldM)

-- ==========================================
-- 1. TYPES
-- ==========================================

data Type 
    = TyInt 
    | TyBool 
    | TyList Type
    -- We might need a generic type for empty lists if we don't do full inference
    -- But for now, let's assume lists are typed by their content or context
    | TyAny -- For empty lists/unknowns in this simple prototype
    deriving (Show, Eq)

data TypeError 
    = Mismatch Type Type String -- Expected, Actual, Context
    | NotList Type 
    | UndefinedVar String
    | EmptyListWithoutContext
    deriving (Show, Eq)

type TypeContext = Map String Type

-- ==========================================
-- 2. THE TYPE CHECKER
-- ==========================================

-- Helper to check equality
expect :: Type -> Type -> String -> Either TypeError ()
expect TyAny _ _ = Right () -- TyAny matches anything (polymorphic-ish)
expect _ TyAny _ = Right ()
expect expected actual ctx = 
    if expected == actual 
    then Right () 
    else Left (Mismatch expected actual ctx)

-- The Inference Engine
infer :: Term -> TypeContext -> Either TypeError Type
infer term ctx = case term of
    
    -- Primitives
    IntVal _  -> Right TyInt
    BoolVal _ -> Right TyBool
    
    -- Variables
    Var s -> case Map.lookup s ctx of
        Just t  -> Right t
        Nothing -> Left (UndefinedVar s)
    
    -- Lists (Homogeneous check)
    ListVal [] -> Right (TyList TyAny) -- Empty list is generic
    ListVal (x:xs) -> do
        tHead <- infer x ctx
        -- Check all rest match head
        foldM (\expectedT elem -> do
            tElem <- infer elem ctx
            expect expectedT tElem "List Element"
            return expectedT
            ) tHead xs
        return (TyList tHead)

    -- Arithmetic (Requires Int)
    Add t1 t2 -> do
        t1Type <- infer t1 ctx
        t2Type <- infer t2 ctx
        expect TyInt t1Type "Add Left"
        expect TyInt t2Type "Add Right"
        return TyInt

    Div t1 t2 -> do
        t1Type <- infer t1 ctx
        t2Type <- infer t2 ctx
        expect TyInt t1Type "Div Left"
        expect TyInt t2Type "Div Right"
        return TyInt

    -- Logic (Equality allows any type, but they must match)
    Eq t1 t2 -> do
        t1Type <- infer t1 ctx
        t2Type <- infer t2 ctx
        expect t1Type t2Type "Equality"
        return TyBool

    -- Control Flow
    If cond t1 t2 -> do
        condT <- infer cond ctx
        expect TyBool condT "If Condition"
        t1T <- infer t1 ctx
        t2T <- infer t2 ctx
        expect t1T t2T "If Branches"
        return t1T

    -- Binding
    Let name val body -> do
        valT <- infer val ctx
        infer body (Map.insert name valT ctx)

    -- Data Processing (The Tricky Part!)
    -- Map: Input list [A], Body uses A, Returns B -> Result [B]
    Map var body listTerm -> do
        listT <- infer listTerm ctx
        case listT of
            TyList elemT -> do
                -- Infer body with variable in context
                retT <- infer body (Map.insert var elemT ctx)
                return (TyList retT)
            _ -> Left (NotList listT)

    -- Fold: Input list [A], Init B, Body (B -> A -> B) -> Result B
    Fold accName varName body initTerm listTerm -> do
        initT <- infer initTerm ctx
        listT <- infer listTerm ctx
        case listT of
            TyList elemT -> do
                let bodyCtx = Map.insert accName initT (Map.insert varName elemT ctx)
                bodyT <- infer body bodyCtx
                expect initT bodyT "Fold Accumulator"
                return initT
            _ -> Left (NotList listT)

    -- Loops
    Repeat _ body -> do
        _ <- infer body ctx
        return TyInt -- Repeat currently returns Int (0) in runtime, technically Unit-like? 
                     -- The runtime implementation returns VInt 0.

    -- Error Handling
    Shield try fallback -> do
        t1 <- infer try ctx
        t2 <- infer fallback ctx
        expect t1 t2 "Shield Fallback"
        return t1
        
    Log _ t -> infer t ctx

-- ==========================================
-- 3. THE THERMODYNAMIC COMPILER (Integrated)
-- ==========================================

-- Returns either a Type Error or the valid Thermodynamic Stats
analyzeTyped :: Term -> Either TypeError ProgramStats
analyzeTyped term = 
    case infer term Map.empty of
        Left err -> Left err
        Right _  -> Right (analyze term Map.empty)