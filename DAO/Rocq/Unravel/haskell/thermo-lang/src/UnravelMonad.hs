module UnravelMonad where

import Prelude hiding (div, (/))
import qualified Prelude
import Data.Char (ord, chr)

-- ==========================================
-- 1. THE PRIMITIVE TYPES (Ontology)
-- ==========================================

data VoidSource 
    = DivByZero 
    | LogicError String 
    | RootEntropy 
    | VoidNeutral 
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

data Universe = Universe {
    totalEntropy   :: Int,
    timeStep       :: Int,
    voidCount      :: Int,
    boundaryValue  :: Integer,
    boundaryLength :: Int 
} deriving (Show, Eq)

-- ==========================================
-- 2. THE HOLOGRAPHIC ENCODING (Gödel ASCII)
-- ==========================================

-- Tokens
t_VOID_NEUTRAL :: Integer
t_VOID_NEUTRAL = 0

t_DIV_ZERO :: Integer
t_DIV_ZERO = 1

t_ROOT_ENTROPY :: Integer
t_ROOT_ENTROPY = 2

-- String Delimiters
t_MSG_OPEN :: Integer
t_MSG_OPEN = 30

t_MSG_CLOSE :: Integer
t_MSG_CLOSE = 31

-- Structural Markers 
t_SEQ_OP :: Integer
t_SEQ_OP = 10  

t_MIX_OPEN :: Integer
t_MIX_OPEN = 20 

t_MIX_MID :: Integer
t_MIX_MID = 21  

t_MIX_CLOSE :: Integer
t_MIX_CLOSE = 22 

-- Base 256 
holographicBase :: Integer
holographicBase = 256

-- ENCODER: Tree -> [Tokens]
flattenPath :: ParadoxPath -> [Integer]
flattenPath (BaseVeil src) = case src of
    VoidNeutral -> [] 
    DivByZero -> [t_DIV_ZERO]
    RootEntropy -> [t_ROOT_ENTROPY]
    LogicError msg -> 
        [t_MSG_OPEN] 
        ++ Prelude.map (Prelude.fromIntegral . ord) msg 
        ++ [t_MSG_CLOSE]

flattenPath (SelfContradict p) = 
    [t_SEQ_OP] ++ flattenPath p
flattenPath (Compose p1 p2) = 
    [t_MIX_OPEN] ++ flattenPath p1 ++ [t_MIX_MID] ++ flattenPath p2 ++ [t_MIX_CLOSE]

-- COMPRESSOR: [Tokens] -> Integer (Little Endian: Head is B^0)
compress :: [Integer] -> Integer
compress digits = Prelude.foldr (\d acc -> d Prelude.+ (holographicBase Prelude.* acc)) 0 digits

-- DECOMPRESSOR: Integer -> [Tokens] (Returns Little Endian)
decompress :: Integer -> [Integer]
decompress 0 = []
decompress n = 
    let (rest, digit) = n `Prelude.divMod` holographicBase
    in digit : decompress rest

-- SECURE APPENDER (Chronological)
-- We put Old Value in LOW bits (parsed first)
-- We put New Value in HIGH bits (parsed last)
appendHologram :: Integer -> Int -> Integer -> Int -> (Integer, Int)
appendHologram valOld lenOld valNew lenNew = 
    let shift = holographicBase Prelude.^ lenOld -- Shift by Old length? No, Old is low bits.
        -- Wait. N = Low + High * B^lenLow
        -- We want Old to be Low.
        -- So N = Old + New * B^lenOld
        shiftForNew = holographicBase Prelude.^ lenOld
        newVal = valOld Prelude.+ (valNew Prelude.* shiftForNew)
        newLen = lenOld Prelude.+ lenNew
    in (newVal, newLen)

-- RECONSTRUCTOR PARSERS
parsePath :: [Integer] -> Maybe (ParadoxPath, [Integer])
parsePath [] = Nothing

parsePath (x:xs) | x == t_DIV_ZERO = Just (BaseVeil DivByZero, xs)
parsePath (x:xs) | x == t_ROOT_ENTROPY = Just (BaseVeil RootEntropy, xs)

-- String Parsing
parsePath (x:xs) | x == t_MSG_OPEN = 
    let (msgCodes, rest) = Prelude.break (== t_MSG_CLOSE) xs
    in case rest of
        (_:restAfterClose) -> 
            let msg = Prelude.map (chr . Prelude.fromIntegral) msgCodes
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

-- Public Reconstructor
reconstruct :: Integer -> [ParadoxPath]
reconstruct 0 = []
reconstruct n = 
    -- FIXED: No reverse needed. Decompress returns [Oldest ... Newest]
    let tokens = decompress n
    in case parsePath tokens of
        Just (p, rest) -> 
            -- FIXED: Compress rest directly (it is already in correct order)
            let remainingInt = compress rest
            in p : reconstruct remainingInt
        Nothing -> []

-- ==========================================
-- 3. THE MONAD
-- ==========================================

newtype Unravel a = Unravel { 
    runUnravel :: Universe -> (UResult a, Universe) 
} deriving (Prelude.Functor)

rankOf :: ParadoxPath -> Int
rankOf (BaseVeil VoidNeutral) = 0 
rankOf (BaseVeil _) = 1
rankOf (SelfContradict p) = 1 + rankOf p
rankOf (Compose p1 p2) = rankOf p1 + rankOf p2

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
            
            (Invalid i1, Invalid i2) -> 
                let newPath = Compose (genealogy i1) (genealogy i2)
                    newInfo = VoidInfo newPath
                    
                    pathTokens = flattenPath newPath
                    boundVal   = compress pathTokens
                    boundLen   = Prelude.length pathTokens
                    
                    (finalBound, finalLen) = appendHologram 
                                                (boundaryValue uTimed) (boundaryLength uTimed)
                                                boundVal boundLen
                    
                    uFinal  = uTimed { totalEntropy = totalEntropy uTimed + rankOf newPath 
                                     , voidCount = voidCount uTimed + 1 
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
            
            Invalid i -> 
                let oldPath = genealogy i
                    newPath = SelfContradict oldPath 
                    newInfo = VoidInfo newPath
                    
                    pathTokens = flattenPath newPath
                    boundVal   = compress pathTokens
                    boundLen   = Prelude.length pathTokens
                    
                    (finalBound, finalLen) = appendHologram 
                                                (boundaryValue uTimed) (boundaryLength uTimed)
                                                boundVal boundLen

                    uEvolved = uTimed { boundaryValue = finalBound
                                      , boundaryLength = finalLen } 
                in (Invalid newInfo, uEvolved)

-- ==========================================
-- 4. PRIMITIVES
-- ==========================================

bigBang :: Universe
bigBang = Universe 0 0 0 0 0

run :: Unravel a -> (UResult a, Universe)
run prog = runUnravel prog bigBang

crumble :: VoidSource -> Unravel a
crumble src = Unravel $ \u ->
    let path = BaseVeil src
        info = VoidInfo path
        
        pathTokens = flattenPath path
        boundVal   = compress pathTokens
        boundLen   = Prelude.length pathTokens
        
        (finalBound, finalLen) = appendHologram 
                                    (boundaryValue u) (boundaryLength u)
                                    boundVal boundLen

        u'   = u { totalEntropy = totalEntropy u + rankOf path 
                 , voidCount = voidCount u + 1 
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
        
        (Invalid i1, Invalid i2) -> 
             let newPath = Compose (genealogy i1) (genealogy i2)
                 newInfo = VoidInfo newPath
                 
                 pathTokens = flattenPath newPath
                 boundVal   = compress pathTokens
                 boundLen   = Prelude.length pathTokens
                 
                 (finalBound, finalLen) = appendHologram 
                                            (boundaryValue uFinal) (boundaryLength uFinal)
                                            boundVal boundLen

                 uMerge = uFinal { boundaryValue = finalBound 
                                 , boundaryLength = finalLen }
             in (Invalid newInfo, uMerge)