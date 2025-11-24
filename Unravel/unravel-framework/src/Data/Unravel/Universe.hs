module Data.Unravel.Universe where

import Data.Char (ord, chr)
import Data.Bits (xor, shiftL)

-- ==========================================
-- 1. PHYSICS ONTOLOGY
-- ==========================================

data VoidSource 
    = DivByZero 
    | LogicError String 
    | IOException String  -- NEW: For wrapping real IO errors
    | RootEntropy 
    | VoidNeutral 
    deriving (Show, Eq, Ord)

-- The Causal Tree
data ParadoxPath
    = BaseVeil VoidSource             
    | SelfContradict ParadoxPath      -- Time Evolution
    | Compose ParadoxPath ParadoxPath -- Structural Branching
    deriving (Show, Eq)

-- The State of the World
data Universe = Universe {
    structEntropy  :: Int,     
    timeEntropy    :: Int,     
    timeStep       :: Int,     
    voidCount      :: Int,     
    mass           :: Int,     -- Successful work
    boundaryValue  :: Integer, -- The Hologram
    boundaryLength :: Int      
} deriving (Show, Eq)

emptyUniverse :: Universe
emptyUniverse = Universe 0 0 0 0 0 0 0

-- ==========================================
-- 2. HOLOGRAPHIC ENGINE (Gödel)
-- ==========================================

holographicBase :: Integer
holographicBase = 256

-- [Tokens mapping...]
t_DIV_ZERO, t_IO_ERR, t_LOGIC_ERR :: Integer
t_DIV_ZERO = 1
t_IO_ERR   = 2
t_LOGIC_ERR = 3

t_SEQ, t_MIX_OPEN, t_MIX_MID, t_MIX_CLOSE :: Integer
t_SEQ = 10
t_MIX_OPEN = 20
t_MIX_MID = 21
t_MIX_CLOSE = 22

t_STR_OPEN, t_STR_CLOSE :: Integer
t_STR_OPEN = 30
t_STR_CLOSE = 31

flattenPath :: ParadoxPath -> [Integer]
flattenPath (BaseVeil src) = case src of
    VoidNeutral -> []
    DivByZero -> [t_DIV_ZERO]
    IOException msg -> encodeMsg t_IO_ERR msg
    LogicError msg -> encodeMsg t_LOGIC_ERR msg
    RootEntropy -> [99]
  where
    encodeMsg tag msg = 
        [tag, t_STR_OPEN] 
        ++ map (fromIntegral . ord) msg 
        ++ [t_STR_CLOSE]

flattenPath (SelfContradict p) = [t_SEQ] ++ flattenPath p
flattenPath (Compose p1 p2) = 
    [t_MIX_OPEN] ++ flattenPath p1 ++ [t_MIX_MID] ++ flattenPath p2 ++ [t_MIX_CLOSE]

compress :: [Integer] -> Integer
compress = foldr (\d acc -> d + (holographicBase * acc)) 0

-- Secure Append (Chronological)
appendHologram :: Integer -> Int -> Integer -> Int -> (Integer, Int)
appendHologram valOld lenOld valNew lenNew = 
    let shift = holographicBase ^ lenOld
        newVal = valOld + (valNew * shift)
    in (newVal, lenOld + lenNew)

-- Rank Tensor (Structure, Time)
rankOf :: ParadoxPath -> (Int, Int)
rankOf (BaseVeil VoidNeutral) = (0, 0)
rankOf (BaseVeil _) = (0, 1)
rankOf (SelfContradict p) = let (s, t) = rankOf p in (s, t + 1)
rankOf (Compose p1 p2) = 
    let (s1, t1) = rankOf p1; (s2, t2) = rankOf p2 
    in (s1 + s2 + 1, t1 + t2)