module UnravelMonad where

import Prelude hiding (div, (/))
import Data.Char (ord, chr)

-- ==========================================
-- 1. ONTOLOGY (The Primitive Types)
-- ==========================================

data VoidSource 
    = DivByZero 
    | LogicError String 
    | RootEntropy 
    | VoidNeutral 
    deriving (Show, Eq, Ord)

-- The genealogical tree of failure
data ParadoxPath
    = BaseVeil VoidSource             
    | SelfContradict ParadoxPath      -- Temporal evolution (Next)
    | Compose ParadoxPath ParadoxPath -- Structural entanglement (Mix)
    deriving (Show, Eq)

data VoidInfo = VoidInfo {
    genealogy :: ParadoxPath
} deriving (Show, Eq)

data UResult a 
    = Valid a 
    | Invalid VoidInfo 
    deriving (Show, Eq, Functor)

-- The Physical Universe State
data Universe = Universe {
    structEntropy  :: Int,     -- Complexity (Branching)
    timeEntropy    :: Int,     -- Age (Depth)
    timeStep       :: Int,     -- Global clock
    voidCount      :: Int,     -- Number of singularities encountered
    boundaryValue  :: Integer, -- The Hologram (Gödel Number)
    boundaryLength :: Int      -- Token count for append safety
} deriving (Show, Eq)

-- Helper: Total Scalar Entropy
totalEntropy :: Universe -> Int
totalEntropy u = structEntropy u + timeEntropy u

-- ==========================================
-- 2. HOLOGRAPHIC ENCODING (Gödel ASCII)
-- ==========================================

-- Tokens (Bytecode for the Hologram)
t_VOID_NEUTRAL, t_DIV_ZERO, t_ROOT_ENTROPY :: Integer
t_VOID_NEUTRAL = 0
t_DIV_ZERO     = 1
t_ROOT_ENTROPY = 2

t_MSG_OPEN, t_MSG_CLOSE :: Integer
t_MSG_OPEN  = 30
t_MSG_CLOSE = 31

t_SEQ_OP, t_MIX_OPEN, t_MIX_MID, t_MIX_CLOSE :: Integer
t_SEQ_OP    = 10
t_MIX_OPEN  = 20 
t_MIX_MID   = 21  
t_MIX_CLOSE = 22 

holographicBase :: Integer
holographicBase = 256

-- Encoder: Tree -> [Tokens]
flattenPath :: ParadoxPath -> [Integer]
flattenPath (BaseVeil src) = case src of
    VoidNeutral -> [] 
    DivByZero -> [t_DIV_ZERO]
    RootEntropy -> [t_ROOT_ENTROPY]
    LogicError msg -> 
        [t_MSG_OPEN] 
        ++ map (fromIntegral . ord) msg 
        ++ [t_MSG_CLOSE]

flattenPath (SelfContradict p) = 
    [t_SEQ_OP] ++ flattenPath p
flattenPath (Compose p1 p2) = 
    [t_MIX_OPEN] ++ flattenPath p1 ++ [t_MIX_MID] ++ flattenPath p2 ++ [t_MIX_CLOSE]

-- Compressor: [Tokens] -> Integer (Little Endian: Head is B^0)
compress :: [Integer] -> Integer
compress digits = foldr (\d acc -> d + (holographicBase * acc)) 0 digits

-- Decompressor: Integer -> [Tokens]
decompress :: Integer -> [Integer]
decompress 0 = []
decompress n = 
    let (rest, digit) = n `divMod` holographicBase
    in digit : decompress rest

-- Appender: Concatenates history safely (Old ++ New)
-- Places 'Old' in low bits (parsed first), 'New' in high bits (parsed last)
appendHologram :: Integer -> Int -> Integer -> Int -> (Integer, Int)
appendHologram valOld lenOld valNew lenNew = 
    let shiftForNew = holographicBase ^ lenOld
        newVal = valOld + (valNew * shiftForNew)
        newLen = lenOld + lenNew
    in (newVal, newLen)

-- Parsers for Reconstruction
parsePath :: [Integer] -> Maybe (ParadoxPath, [Integer])
parsePath [] = Nothing

parsePath (x:xs) | x == t_DIV_ZERO = Just (BaseVeil DivByZero, xs)
parsePath (x:xs) | x == t_ROOT_ENTROPY = Just (BaseVeil RootEntropy, xs)

parsePath (x:xs) | x == t_MSG_OPEN = 
    let (msgCodes, rest) = break (== t_MSG_CLOSE) xs
    in case rest of
        (_:restAfterClose) -> 
            let msg = map (chr . fromIntegral) msgCodes
            in Just (BaseVeil (LogicError msg), restAfterClose)
        [] -> Nothing 

parsePath (x:xs) | x == t_SEQ_OP = do
    (p, rest) <- parsePath xs
    Just (SelfContradict p, rest)

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

-- Public Reconstructor: Integer -> History [Oldest ... Newest]
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
-- 3. THE UNRAVEL MONAD & TENSOR RANK
-- ==========================================

newtype Unravel a = Unravel { 
    runUnravel :: Universe -> (UResult a, Universe) 
} deriving (Functor)

-- Rank Tensor: (Structural, Temporal)
rankOf :: ParadoxPath -> (Int, Int)
rankOf (BaseVeil VoidNeutral) = (0, 0)
rankOf (BaseVeil _) = (0, 1) -- Atomic event: 1 unit of time depth
rankOf (SelfContradict p) = 
    let (s, t) = rankOf p 
    in (s, t + 1)
rankOf (Compose p1 p2) = 
    let (s1, t1) = rankOf p1
        (s2, t2) = rankOf p2
    in (s1 + s2 + 1, t1 + t2)

combineVoids :: VoidInfo -> VoidInfo -> VoidInfo
combineVoids (VoidInfo p1) (VoidInfo p2) = 
    VoidInfo (Compose p1 p2)

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
            
            -- STRUCTURAL MERGE
            (Invalid i1, Invalid i2) -> 
                let newPath = Compose (genealogy i1) (genealogy i2)
                    newInfo = VoidInfo newPath
                    (dS, dT) = rankOf newPath
                    
                    pathTokens = flattenPath newPath
                    boundVal   = compress pathTokens
                    boundLen   = length pathTokens
                    
                    (finalBound, finalLen) = appendHologram 
                                                (boundaryValue uTimed) (boundaryLength uTimed)
                                                boundVal boundLen
                    
                    -- Add full tensor rank of new structure
                    uFinal  = uTimed { structEntropy = structEntropy uTimed + dS
                                     , timeEntropy   = timeEntropy uTimed + dT
                                     , voidCount     = voidCount uTimed + 1 
                                     , boundaryValue = finalBound
                                     , boundaryLength = finalLen }
                in (Invalid newInfo, uFinal)

instance Monad Unravel where
    return = pure
    
    (Unravel x) >>= f = Unravel $ \u ->
        let (res, u') = x u 
            uTimed = u' { timeStep = timeStep u' + 1 } 
        in case res of
            Valid val -> runUnravel (f val) uTimed
            
            -- TIME EVOLUTION
            Invalid i -> 
                let oldPath = genealogy i
                    newPath = SelfContradict oldPath 
                    newInfo = VoidInfo newPath
                    
                    pathTokens = flattenPath newPath
                    boundVal   = compress pathTokens
                    boundLen   = length pathTokens
                    
                    (finalBound, finalLen) = appendHologram 
                                                (boundaryValue uTimed) (boundaryLength uTimed)
                                                boundVal boundLen

                    -- Update: Only increment Time entropy by 1.
                    -- We don't re-add the entropy of the oldPath.
                    uEvolved = uTimed { boundaryValue = finalBound
                                      , boundaryLength = finalLen 
                                      , structEntropy = structEntropy uTimed 
                                      , timeEntropy = timeEntropy uTimed + 1 
                                      } 
                in (Invalid newInfo, uEvolved)

-- ==========================================
-- 4. PRIMITIVES
-- ==========================================

bigBang :: Universe
bigBang = Universe 0 0 0 0 0 0

run :: Unravel a -> (UResult a, Universe)
run prog = runUnravel prog bigBang

crumble :: VoidSource -> Unravel a
crumble src = Unravel $ \u ->
    let path = BaseVeil src
        info = VoidInfo path
        (dS, dT) = rankOf path
        
        pathTokens = flattenPath path
        boundVal   = compress pathTokens
        boundLen   = length pathTokens
        
        (finalBound, finalLen) = appendHologram 
                                    (boundaryValue u) (boundaryLength u)
                                    boundVal boundLen

        u'   = u { structEntropy = structEntropy u + dS
                 , timeEntropy   = timeEntropy u + dT
                 , voidCount     = voidCount u + 1 
                 , boundaryValue = finalBound
                 , boundaryLength = finalLen }
    in (Invalid info, u')

currentEntropy :: Unravel Int
currentEntropy = Unravel $ \u -> (Valid (totalEntropy u), u)

getHologram :: Unravel Integer
getHologram = Unravel $ \u -> (Valid (boundaryValue u), u)

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
        
        -- HARVEST MERGE
        (Invalid i1, Invalid i2) -> 
             let newPath = Compose (genealogy i1) (genealogy i2)
                 newInfo = VoidInfo newPath
                 (dS, dT) = rankOf newPath
                 
                 pathTokens = flattenPath newPath
                 boundVal   = compress pathTokens
                 boundLen   = length pathTokens
                 
                 (finalBound, finalLen) = appendHologram 
                                            (boundaryValue uFinal) (boundaryLength uFinal)
                                            boundVal boundLen

                 uMerge = uFinal { boundaryValue = finalBound 
                                 , boundaryLength = finalLen
                                 , structEntropy = structEntropy uFinal + dS
                                 , timeEntropy = timeEntropy uFinal + dT }
             in (Invalid newInfo, uMerge)

-- ==========================================
-- 5. THE TIME MACHINE (Reversible Stepper)
-- ==========================================

stepBackward :: Universe -> Maybe Universe
stepBackward u 
    | boundaryValue u == 0 = Nothing 
    | otherwise = 
        -- Reconstruct returns [Oldest ... Newest]
        let history = reconstruct (boundaryValue u)
        in case reverse history of -- [Newest ... Oldest]
            [] -> Nothing
            (lastEvent : previousEvents) -> 
                let (dS, dT) = rankOf lastEvent
                    
                    -- Rebuild the boundary from [Oldest ... 2ndNewest]
                    -- We reverse previousEvents to get back to [Oldest ... 2ndNewest]
                    prevBoundList = concatMap flattenPath (reverse previousEvents)
                    prevBoundVal  = compress prevBoundList
                    prevBoundLen  = length prevBoundList
                    
                in Just u {
                    structEntropy = structEntropy u - dS,
                    timeEntropy   = timeEntropy u - dT,
                    voidCount     = voidCount u - 1,
                    boundaryValue = prevBoundVal,
                    boundaryLength = prevBoundLen
                }