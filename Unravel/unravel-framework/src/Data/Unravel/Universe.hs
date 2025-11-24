module Data.Unravel.Universe where

import Data.Char (ord, chr)

-- ==========================================
-- 1. PHYSICS ONTOLOGY
-- ==========================================

data VoidSource 
    = DivByZero 
    | LogicError String 
    | IOException String
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
t_VOID_NEUTRAL, t_DIV_ZERO, t_ROOT_ENTROPY, t_IO_ERR, t_LOGIC_ERR :: Integer
t_VOID_NEUTRAL = 0
t_DIV_ZERO     = 1
t_IO_ERR       = 2
t_LOGIC_ERR    = 3
t_ROOT_ENTROPY = 99

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
    RootEntropy -> [t_ROOT_ENTROPY]
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
-- Old in Low bits, New in High bits
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

-- ==========================================
-- 3. RECONSTRUCTION (The Time Machine)
-- ==========================================

decompress :: Integer -> [Integer]
decompress 0 = []
decompress n = 
    let (rest, digit) = n `divMod` holographicBase
    in digit : decompress rest

parsePath :: [Integer] -> Maybe (ParadoxPath, [Integer])
parsePath [] = Nothing

parsePath (x:xs) | x == t_DIV_ZERO = Just (BaseVeil DivByZero, xs)
parsePath (x:xs) | x == t_ROOT_ENTROPY = Just (BaseVeil RootEntropy, xs)

-- String Parsing
parsePath (x:xs) | x == t_IO_ERR || x == t_LOGIC_ERR = 
    case xs of
        (open:rest) | open == t_STR_OPEN -> 
            let (msgCodes, afterMsg) = break (== t_STR_CLOSE) rest
            in case afterMsg of
                (_:restAfterClose) -> 
                    let msg = map (chr . fromIntegral) msgCodes
                        ctor = if x == t_IO_ERR then IOException else LogicError
                    in Just (BaseVeil (ctor msg), restAfterClose)
                [] -> Nothing
        _ -> Nothing

-- FIXED: Use the global constant t_SEQ
parsePath (x:xs) | x == t_SEQ = do
    (p, rest) <- parsePath xs
    Just (SelfContradict p, rest)

-- FIXED: Use global constants for Mix
parsePath (x:xs) | x == t_MIX_OPEN = do
    (p1, rest1) <- parsePath xs
    case rest1 of
        (m:rest2) | m == t_MIX_MID -> do
            (p2, rest3) <- parsePath rest2
            case rest3 of
                (c:rest4) | c == t_MIX_CLOSE -> Just (Compose p1 p2, rest4)
                _ -> Nothing
        _ -> Nothing

parsePath _ = Nothing

-- | Reconstructs the full causal history from the boundary integer
reconstruct :: Integer -> [ParadoxPath]
reconstruct 0 = []
reconstruct n = 
    let tokens = decompress n
    in case parsePath tokens of
        Just (p, rest) -> 
            let remainingInt = compress rest
            in p : reconstruct remainingInt
        Nothing -> []

-- ==========================================
-- 4. PHYSICS METRICS
-- ==========================================

-- | S: Total Entropy
getS :: Universe -> Double
getS u = fromIntegral (structEntropy u + timeEntropy u)

-- | S_dot: Entropy Rate (S / t)
getSdot :: Universe -> Double
getSdot u = 
    let t = fromIntegral (timeStep u)
    in if t > 0 then getS u / t else 0

-- | L: Lagrangian Action (S * S_dot)
getLagrangian :: Universe -> Double
getLagrangian u = getS u * getSdot u