module UnravelMonad where

import Prelude hiding (div, (/))
import qualified Prelude

-- ==========================================
-- 1. THE PRIMITIVE TYPES (Ontology)
-- ==========================================

data VoidSource 
    = DivByZero 
    | LogicError String 
    | RootEntropy 
    deriving (Show, Eq, Ord)

-- THE PERIODIC TABLE OF PARADOX
-- We map fundamental singularities to Prime Numbers.
-- This allows for unique factorization (Reversibility).
primeOf :: VoidSource -> Integer
primeOf DivByZero = 2
primeOf RootEntropy = 3
primeOf (LogicError "Collapsed Infinity") = 5
primeOf (LogicError "Collapsed Nullity") = 7
primeOf (LogicError _) = 11 -- Generic logic errors clump here for now

data ParadoxPath
    = BaseVeil VoidSource             
    | SelfContradict ParadoxPath      
    | Compose ParadoxPath ParadoxPath 
    deriving (Show, Eq)

-- Rank calculation (Thermodynamic Weight)
entropyOf :: ParadoxPath -> Int
entropyOf (BaseVeil _) = 1
entropyOf (SelfContradict p) = 1 + entropyOf p
entropyOf (Compose p1 p2) = entropyOf p1 + entropyOf p2

data VoidInfo = VoidInfo {
    genealogy :: ParadoxPath
} deriving (Show, Eq)

data UResult a 
    = Valid a 
    | Invalid VoidInfo 
    deriving (Show, Eq, Prelude.Functor)

data Universe = Universe {
    totalEntropy :: Int,
    timeStep     :: Int,
    voidCount    :: Int,
    -- NEW: The Reversible Holographic Boundary (Product of Primes)
    boundary     :: Integer
} deriving (Show, Eq)

-- ==========================================
-- 2. THE DREAM MONAD (The Container)
-- ==========================================

newtype Unravel a = Unravel { 
    runUnravel :: Universe -> (UResult a, Universe) 
} deriving (Prelude.Functor)

combineVoids :: VoidInfo -> VoidInfo -> VoidInfo
combineVoids (VoidInfo p1) (VoidInfo p2) = 
    VoidInfo (Compose p1 p2)

-- Entangle: The Universe remembers the Event via Multiplication
-- This is commutative, so order is lost, but content is conserved perfectly.
entangle :: Integer -> VoidSource -> Integer
entangle current src = current * (primeOf src)

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
                    -- Note: The Universe state u'' ALREADY contains the prime factors 
                    -- from running f and x. We don't need to multiply again here,
                    -- or we would double-count. We only add the structural entropy.
                    uFinal  = uTimed { totalEntropy = totalEntropy uTimed + entropyOf (genealogy newVoid) 
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
-- 3. THE PRIMITIVES (The API)
-- ==========================================

bigBang :: Universe
bigBang = Universe 0 0 0 1 -- Init boundary at 1 (Identity)

run :: Unravel a -> (UResult a, Universe)
run prog = runUnravel prog bigBang

-- The Event Generator
crumble :: VoidSource -> Unravel a
crumble src = Unravel $ \u ->
    let path = BaseVeil src
        info = VoidInfo path
        -- CRITICAL: This is where the Event is recorded in the Hologram
        u'   = u { totalEntropy = totalEntropy u + 1 
                 , voidCount = voidCount u + 1 
                 , boundary = entangle (boundary u) src }
    in (Invalid info, u')

currentEntropy :: Unravel Int
currentEntropy = Unravel $ \u -> (Valid (totalEntropy u), u)

getHologram :: Unravel Integer
getHologram = Unravel $ \u -> (Valid (boundary u), u)

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
        (Invalid i1, Invalid i2) -> 
             let combined = combineVoids i1 i2 
             in (Invalid combined, uFinal)

-- ==========================================
-- 4. THE TIME MACHINE (Reconstructor)
-- ==========================================

-- Inverse of primeOf
sourceFromPrime :: Integer -> Maybe VoidSource
sourceFromPrime 2 = Just DivByZero
sourceFromPrime 3 = Just RootEntropy
sourceFromPrime 5 = Just (LogicError "Collapsed Infinity")
sourceFromPrime 7 = Just (LogicError "Collapsed Nullity")
sourceFromPrime 11 = Just (LogicError "Generic Logic Error")
sourceFromPrime _ = Nothing

-- The Factorization Loop
reconstruct :: Integer -> [VoidSource]
reconstruct 1 = []
reconstruct n = 
    let factors = [2, 3, 5, 7, 11]
        found = Prelude.filter (\p -> n `Prelude.rem` p == 0) factors
    in case found of
        [] -> [] -- Should not happen if system is closed
        (p:_) -> case sourceFromPrime p of
            Just src -> src : reconstruct (n `Prelude.div` p)
            Nothing -> []