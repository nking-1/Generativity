module UnravelMonad where

import Prelude hiding (div, (/))
import Data.Bits (xor, shiftL, shiftR)

-- ==========================================
-- 1. THE PRIMITIVE TYPES (Ontology)
-- ==========================================

data VoidSource 
    = DivByZero 
    | LogicError String 
    | RootEntropy 
    deriving (Show, Eq)

data ParadoxPath
    = BaseVeil VoidSource             
    | SelfContradict ParadoxPath      
    | Compose ParadoxPath ParadoxPath 
    deriving (Show, Eq)

-- "Rank" calculation
entropyOf :: ParadoxPath -> Int
entropyOf (BaseVeil _) = 1
entropyOf (SelfContradict p) = 1 + entropyOf p
entropyOf (Compose p1 p2) = entropyOf p1 + entropyOf p2

-- "Holographic" Hash calculation (Rolling hash)
hashPath :: ParadoxPath -> Int
hashPath (BaseVeil src) = case src of
    DivByZero -> 101
    LogicError s -> length s
    RootEntropy -> 999
hashPath (SelfContradict p) = (hashPath p `shiftL` 1) `xor` 0xABC
hashPath (Compose p1 p2) = hashPath p1 `xor` (hashPath p2 `shiftR` 1)

data VoidInfo = VoidInfo {
    genealogy :: ParadoxPath
} deriving (Show, Eq)

data UResult a 
    = Valid a 
    | Invalid VoidInfo 
    deriving (Show, Eq, Functor)

data Universe = Universe {
    totalEntropy :: Int,
    timeStep     :: Int,
    voidCount    :: Int,
    -- NEW: The Holographic Boundary (AdS/CFT Trace)
    boundaryHash :: Int
} deriving (Show, Eq)

-- ==========================================
-- 2. THE DREAM MONAD (The Container)
-- ==========================================

newtype Unravel a = Unravel { 
    runUnravel :: Universe -> (UResult a, Universe) 
} deriving (Functor)

combineVoids :: VoidInfo -> VoidInfo -> VoidInfo
combineVoids (VoidInfo p1) (VoidInfo p2) = 
    VoidInfo (Compose p1 p2)

-- Helper to mix state into the hologram
entangle :: Int -> Int -> Int
entangle current newInfo = 
    (current `shiftL` 3) `xor` newInfo `xor` 0xDEADBEEF

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
                    pathHash = hashPath (genealogy newVoid)
                    uFinal  = uTimed { totalEntropy = totalEntropy uTimed + entropyOf (genealogy newVoid) 
                                     , voidCount = voidCount uTimed + 1 
                                     , boundaryHash = entangle (boundaryHash uTimed) pathHash }
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
bigBang = Universe 0 0 0 0 -- Init hash 0

run :: Unravel a -> (UResult a, Universe)
run prog = runUnravel prog bigBang

crumble :: VoidSource -> Unravel a
crumble src = Unravel $ \u ->
    let path = BaseVeil src
        info = VoidInfo path
        h    = hashPath path
        u'   = u { totalEntropy = totalEntropy u + 1 
                 , voidCount = voidCount u + 1 
                 , boundaryHash = entangle (boundaryHash u) h }
    in (Invalid info, u')

currentEntropy :: Unravel Int
currentEntropy = Unravel $ \u -> (Valid (totalEntropy u), u)

-- NEW: Access the Hologram
getHologram :: Unravel Int
getHologram = Unravel $ \u -> (Valid (boundaryHash u), u)

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