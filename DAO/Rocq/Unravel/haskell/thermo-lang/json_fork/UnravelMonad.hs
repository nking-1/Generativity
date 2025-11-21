module UnravelMonad where

import Prelude hiding (div, (/))
import qualified Prelude

-- ==========================================
-- 1. ONTOLOGY
-- ==========================================

data VoidSource 
    = DivByZero 
    | LogicError String 
    | JsonError String      -- NEW: Parsing/Field access errors
    | Propagation VoidSource VoidSource 
    | RootEntropy 
    deriving (Show, Eq)

data VoidInfo = VoidInfo {
    entropy :: Int,
    source  :: VoidSource
} deriving (Show, Eq)

data UResult a 
    = Valid a 
    | Invalid VoidInfo 
    deriving (Show, Eq, Prelude.Functor)

data Universe = Universe {
    totalEntropy :: Int,
    timeStep     :: Int,
    voidCount    :: Int
} deriving (Show, Eq)

-- ==========================================
-- 2. THE MONAD
-- ==========================================

newtype Unravel a = Unravel { 
    runUnravel :: Universe -> (UResult a, Universe) 
} deriving (Prelude.Functor)

combineVoids :: VoidInfo -> VoidInfo -> VoidInfo
combineVoids (VoidInfo e1 s1) (VoidInfo e2 s2) = 
    VoidInfo (e1 + e2) (Propagation s1 s2)

instance Applicative Unravel where
    pure x = Unravel $ \u -> (Valid x, u)
    
    (Unravel f) <*> (Unravel x) = Unravel $ \u ->
        let (resF, u')  = f u
            (resX, u'') = x u' 
            uTimed      = u'' { timeStep = timeStep u'' + 1 }
        in case (resF, resX) of
            (Valid func, Valid val) -> (Valid (func val), uTimed)
            (Invalid i, Valid _)    -> (Invalid i, uTimed)
            (Valid _, Invalid i)    -> (Invalid i, uTimed)
            (Invalid i1, Invalid i2) -> 
                let newVoid = combineVoids i1 i2
                    uFinal  = uTimed { totalEntropy = totalEntropy uTimed + entropy newVoid 
                                     , voidCount = voidCount uTimed + 1 }
                in (Invalid newVoid, uFinal)

instance Monad Unravel where
    return = pure
    (Unravel x) >>= f = Unravel $ \u ->
        let (res, u') = x u 
            uTimed = u' { timeStep = timeStep u' + 1 } 
        in case res of
            Valid val -> runUnravel (f val) uTimed
            Invalid i -> (Invalid i, uTimed)

-- ==========================================
-- 3. API
-- ==========================================

bigBang :: Universe
bigBang = Universe 0 0 0

run :: Unravel a -> (UResult a, Universe)
run prog = runUnravel prog bigBang

crumble :: VoidSource -> Unravel a
crumble src = Unravel $ \u ->
    let info = VoidInfo 1 src 
        u'   = u { totalEntropy = totalEntropy u + 1 
                 , voidCount = voidCount u + 1 }
    in (Invalid info, u')

uDiv :: Int -> Int -> Unravel Int
uDiv _ 0 = crumble DivByZero
uDiv n d = return (n `Prelude.div` d)

(|+|) :: Unravel Int -> Unravel Int -> Unravel Int
x |+| y = (Prelude.+) Prelude.<$> x Prelude.<*> y

(|*|) :: Unravel Int -> Unravel Int -> Unravel Int
x |*| y = (Prelude.*) Prelude.<$> x Prelude.<*> y

recover :: Unravel a -> a -> Unravel a
recover (Unravel op) defaultVal = Unravel $ \u ->
    let (res, u') = op u 
    in case res of
        Valid v   -> (Valid v, u')
        Invalid _ -> (Valid defaultVal, u') 

harvest :: [Unravel a] -> Unravel [a]
harvest [] = return []
harvest (x:xs) = Unravel $ \u ->
    let (res, u') = runUnravel x u
        (resRest, uFinal) = runUnravel (harvest xs) u'
    in case (res, resRest) of
        (Valid val, Valid rest) -> (Valid (val : rest), uFinal)
        (Invalid _, Valid rest) -> (Valid rest, uFinal)
        (Valid _, Invalid i)    -> (Invalid i, uFinal)
        (Invalid _, Invalid i)  -> (Invalid i, uFinal)