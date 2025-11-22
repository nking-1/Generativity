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

data ParadoxPath
    = BaseVeil VoidSource             
    | SelfContradict ParadoxPath      
    | Compose ParadoxPath ParadoxPath 
    deriving (Show, Eq)

data VoidInfo = VoidInfo {
    genealogy :: ParadoxPath
} deriving (Show, Eq)

data UResult a 
    = Valid a 
    | Invalid VoidInfo 
    deriving (Show, Eq, Prelude.Functor)

-- The Hologram is now an infinite-precision Integer acting as a Gödel Number
data Universe = Universe {
    totalEntropy :: Int,
    timeStep     :: Int,
    voidCount    :: Int,
    boundary     :: Integer 
} deriving (Show, Eq)

-- ==========================================
-- 2. THE HOLOGRAPHIC ENCODING (Gödel Numbering)
-- ==========================================

-- Tokens
t_DIV_ZERO :: Integer
t_DIV_ZERO = 1

t_ROOT_ENTROPY :: Integer
t_ROOT_ENTROPY = 2

t_LOGIC_ERR :: Integer
t_LOGIC_ERR = 3 

-- Structural Markers 
t_SEQ_OP :: Integer
t_SEQ_OP = 10  

t_MIX_OPEN :: Integer
t_MIX_OPEN = 20 

t_MIX_MID :: Integer
t_MIX_MID = 21  

t_MIX_CLOSE :: Integer
t_MIX_CLOSE = 22 

-- Base 100 for readable digits
holographicBase :: Integer
holographicBase = 100

-- ENCODER: Tree -> [Tokens]
flattenPath :: ParadoxPath -> [Integer]
flattenPath (BaseVeil src) = case src of
    DivByZero -> [t_DIV_ZERO]
    RootEntropy -> [t_ROOT_ENTROPY]
    LogicError _ -> [t_LOGIC_ERR] 
flattenPath (SelfContradict p) = 
    [t_SEQ_OP] ++ flattenPath p
flattenPath (Compose p1 p2) = 
    [t_MIX_OPEN] ++ flattenPath p1 ++ [t_MIX_MID] ++ flattenPath p2 ++ [t_MIX_CLOSE]

-- COMPRESSOR: [Tokens] -> Integer
-- d0 + d1*B + d2*B^2 ...
compress :: [Integer] -> Integer
compress digits = Prelude.foldr (\d acc -> d Prelude.+ (holographicBase Prelude.* acc)) 0 digits

-- DECOMPRESSOR: Integer -> [Tokens]
decompress :: Integer -> [Integer]
decompress 0 = []
decompress n = 
    let (rest, digit) = n `Prelude.divMod` holographicBase
    in digit : decompress rest

-- APPENDER: Combines two holograms (H_old ++ H_new)
-- This requires knowing the "length" (magnitude) of H_new to shift H_old correctly.
-- Since we don't track length, we'll cheat slightly by decompressing H_new only.
-- Ideally we'd track (Integer, Int) for (Value, Length).
appendHologram :: Integer -> Integer -> Integer
appendHologram old new = 
    let newTokens = decompress new -- This is reversed (least significant first)
        shift     = (holographicBase Prelude.^ (Prelude.length newTokens))
    in new Prelude.+ (old Prelude.* shift)

-- RECONSTRUCTOR: [Tokens] -> (ParadoxPath, RemainingTokens)
parsePath :: [Integer] -> Maybe (ParadoxPath, [Integer])
parsePath [] = Nothing

-- Atomic
parsePath (x:xs) | x == t_DIV_ZERO = Just (BaseVeil DivByZero, xs)
parsePath (x:xs) | x == t_ROOT_ENTROPY = Just (BaseVeil RootEntropy, xs)
parsePath (x:xs) | x == t_LOGIC_ERR = Just (BaseVeil (LogicError "Unknown"), xs)

-- Sequence (Next p)
parsePath (x:xs) | x == t_SEQ_OP = do
    (p, rest) <- parsePath xs
    Just (SelfContradict p, rest)

-- Branch (Compose p1 p2)
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

-- The Public Reconstructor Function
-- Returns a LIST of paths because the boundary accumulates multiple events
reconstruct :: Integer -> [ParadoxPath]
reconstruct 0 = []
reconstruct n = 
    let tokens = Prelude.reverse (decompress n) -- Fix endianness for parsing
    in case parsePath tokens of
        Just (p, rest) -> 
            -- If we found a path, we need to process the rest of the tokens
            -- Convert remaining tokens back to integer to recurse (inefficient but correct for v0.6)
            let remainingInt = compress (Prelude.reverse rest)
            in p : reconstruct remainingInt
        Nothing -> [] -- Garbled history or done

-- ==========================================
-- 3. THE MONAD
-- ==========================================

newtype Unravel a = Unravel { 
    runUnravel :: Universe -> (UResult a, Universe) 
} deriving (Prelude.Functor)

-- Entropy Rank
rankOf :: ParadoxPath -> Int
rankOf (BaseVeil _) = 1
rankOf (SelfContradict p) = 1 + rankOf p
rankOf (Compose p1 p2) = rankOf p1 + rankOf p2

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
                let newPath = Compose (genealogy i1) (genealogy i2)
                    newInfo = VoidInfo newPath
                    newBoundary = compress (flattenPath newPath)
                    
                    -- APPEND, DON'T REPLACE
                    uFinal  = uTimed { totalEntropy = totalEntropy uTimed + rankOf newPath 
                                     , voidCount = voidCount uTimed + 1 
                                     , boundary = appendHologram (boundary uTimed) newBoundary }
                in (Invalid newInfo, uFinal)

instance Monad Unravel where
    return = pure
    
    (Unravel x) >>= f = Unravel $ \u ->
        let (res, u') = x u 
            uTimed = u' { timeStep = timeStep u' + 1 } 
        in case res of
            Valid val -> runUnravel (f val) uTimed
            
            Invalid i -> 
                let oldPath = genealogy i
                    newPath = SelfContradict oldPath 
                    newInfo = VoidInfo newPath
                    newBoundary = compress (flattenPath newPath)
                    
                    -- Note: Here we conceptually "Replace" because we are evolving the *same* error 
                    -- forward in time, not adding a new one. However, if we want to keep the 
                    -- full history trace, we should probably append too.
                    -- For v0.6, we will just append the *new evolution* to the log.
                    uEvolved = uTimed { boundary = appendHologram (boundary uTimed) newBoundary } 
                in (Invalid newInfo, uEvolved)

-- ==========================================
-- 4. PRIMITIVES
-- ==========================================

bigBang :: Universe
bigBang = Universe 0 0 0 0

run :: Unravel a -> (UResult a, Universe)
run prog = runUnravel prog bigBang

crumble :: VoidSource -> Unravel a
crumble src = Unravel $ \u ->
    let path = BaseVeil src
        info = VoidInfo path
        bound = compress (flattenPath path)
        
        -- CRITICAL FIX: Append to history, don't overwrite!
        u'   = u { totalEntropy = totalEntropy u + 1 
                 , voidCount = voidCount u + 1 
                 , boundary = appendHologram (boundary u) bound }
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
             let newPath = Compose (genealogy i1) (genealogy i2)
                 newInfo = VoidInfo newPath
                 newBoundary = compress (flattenPath newPath)
                 -- Append here too
                 uMerge = uFinal { boundary = appendHologram (boundary uFinal) newBoundary }
             in (Invalid newInfo, uMerge)