module ThermoTypeSystem where

import ThermoLang
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (foldM)

data Type 
    = TyInt 
    | TyBool 
    | TyList Type 
    | TyFunc [Type] Type -- Basic Function Type support
    | TyAny 
    deriving (Show, Eq)

data TypeError 
    = Mismatch Type Type String 
    | NotList Type 
    | UndefinedVar String 
    | EmptyListWithoutContext
    | NotFunction Type
    deriving (Show, Eq)

type TypeContext = Map String Type

expect :: Type -> Type -> String -> Either TypeError ()
expect TyAny _ _ = Right () 
expect _ TyAny _ = Right ()
expect expected actual ctx = 
    if expected == actual 
    then Right () 
    else Left (Mismatch expected actual ctx)

infer :: Term -> TypeContext -> Either TypeError Type
infer term ctx = case term of
    
    IntVal _  -> Right TyInt
    BoolVal _ -> Right TyBool
    
    Var s -> case Map.lookup s ctx of
        Just t  -> Right t
        Nothing -> Left (UndefinedVar s)
    
    -- Functions: We infer arguments as TyAny in the body context for flexibility
    Fn args body -> do
        let argCtx = foldr (\arg m -> Map.insert arg TyAny m) ctx args
        retType <- infer body argCtx
        let argTypes = replicate (length args) TyAny
        return (TyFunc argTypes retType)

    Call f args -> do
        fType <- infer f ctx
        case fType of
            TyFunc _ ret -> do 
                -- We don't strictly check arg types against TyAny placeholders yet
                _ <- mapM (\a -> infer a ctx) args
                return ret
            TyAny -> Right TyAny
            _ -> Left (NotFunction fType)

    ListVal [] -> Right (TyList TyAny) 
    ListVal (x:xs) -> do
        tHead <- infer x ctx
        -- Relaxed typing for heterogeneous lists (dashboards)
        finalType <- foldM (\currentT el -> do
            tElem <- infer el ctx
            if currentT == tElem || currentT == TyAny 
                then return tElem 
                else return TyAny
            ) tHead xs
        
        if finalType == TyAny 
            then return (TyList TyAny)
            else return (TyList finalType)

    -- Arithmetic
    Add t1 t2 -> checkMath t1 t2 "Add" ctx
    Sub t1 t2 -> checkMath t1 t2 "Sub" ctx
    Mul t1 t2 -> checkMath t1 t2 "Mul" ctx
    Div t1 t2 -> checkMath t1 t2 "Div" ctx

    -- Logic & Comparison
    Eq t1 t2 -> do
        t1Type <- infer t1 ctx
        t2Type <- infer t2 ctx
        return TyBool -- Equality works on everything

    Lt t1 t2 -> checkCompare t1 t2 "LessThan" ctx
    Gt t1 t2 -> checkCompare t1 t2 "GreaterThan" ctx

    If cond t1 t2 -> do
        condT <- infer cond ctx
        expect TyBool condT "If Condition"
        t1T <- infer t1 ctx
        t2T <- infer t2 ctx
        if t1T == t2T then return t1T else return TyAny

    Let name val body -> do
        valT <- infer val ctx
        infer body (Map.insert name valT ctx)

    Map var body listTerm -> do
        listT <- infer listTerm ctx
        case listT of
            TyList elemT -> do
                retT <- infer body (Map.insert var elemT ctx)
                return (TyList retT)
            _ -> Left (NotList listT)

    Fold accName varName body initTerm listTerm -> do
        initT <- infer initTerm ctx
        listT <- infer listTerm ctx
        case listT of
            TyList elemT -> do
                let bodyCtx = Map.insert accName initT (Map.insert varName elemT ctx)
                bodyT <- infer body bodyCtx
                if initT == bodyT then return initT else return TyAny
            _ -> Left (NotList listT)

    Repeat nTerm body -> do
        nType <- infer nTerm ctx
        expect TyInt nType "Repeat Count"
        _ <- infer body ctx
        return TyInt 

    Shield try fallback -> do
        t1 <- infer try ctx
        t2 <- infer fallback ctx
        if t1 == t2 then return t1 else return TyAny
        
    Log _ t -> infer t ctx

    -- Observables
    GetEntropy -> Right TyInt
    GetStruct -> Right TyInt
    GetTime -> Right TyInt
    GetVoids -> Right TyInt
    GetTicks -> Right TyInt
    GetHologram -> Right TyInt
    GetMass -> Right TyInt
    GetRate -> Right TyInt
    GetDensity -> Right TyInt
    SetGasLimit t -> do
        tType <- infer t ctx
        expect TyInt tType "GasLimit"
        return TyInt
    
    Evolve t -> do
        tType <- infer t ctx
        expect TyInt tType "Evolve Time"
        return TyInt

checkMath :: Term -> Term -> String -> TypeContext -> Either TypeError Type
checkMath t1 t2 op ctx = do
    t1Type <- infer t1 ctx
    t2Type <- infer t2 ctx
    expect TyInt t1Type (op ++ " Left")
    expect TyInt t2Type (op ++ " Right")
    return TyInt

checkCompare :: Term -> Term -> String -> TypeContext -> Either TypeError Type
checkCompare t1 t2 op ctx = do
    t1Type <- infer t1 ctx
    t2Type <- infer t2 ctx
    expect TyInt t1Type (op ++ " Left")
    expect TyInt t2Type (op ++ " Right")
    return TyBool

analyzeTyped :: Term -> Either TypeError ProgramStats
analyzeTyped term = 
    case infer term Map.empty of
        Left err -> Left err
        Right _  -> Right (analyze term Map.empty)