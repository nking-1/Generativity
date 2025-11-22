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
    | SelfContradict ParadoxPath      -- Adds Temporal Entropy
    | Compose ParadoxPath ParadoxPath -- Adds Structural Entropy
    deriving (Show, Eq)

data VoidInfo = VoidInfo {
    genealogy :: ParadoxPath
} deriving (Show, Eq)

data UResult a 
    = Valid a 
    | Invalid VoidInfo 
    deriving (Show, Eq, Prelude.Functor)

-- NEW: The Physical Universe State
data Universe = Universe {
    -- The Entropy Tensor
    structEntropy  :: Int,     -- Branching / Entanglement complexity
    timeEntropy    :: Int,     -- Temporal depth of paradoxes
    
    timeStep       :: Int,
    voidCount      :: Int,
    boundaryValue  :: Integer,
    boundaryLength :: Int 
} deriving (Show, Eq)

-- Helper to get total scalar entropy
totalEntropy :: Universe -> Int
totalEntropy u = structEntropy u Prelude.+ timeEntropy u

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

t_MSG_OPEN :: Integer
t_MSG_OPEN = 30

t_MSG_CLOSE :: Integer
t_MSG_CLOSE = 31

t_SEQ_OP :: Integer
t_SEQ_OP = 10  

t_MIX_OPEN :: Integer
t_MIX_OPEN = 20 

t_MIX_MID :: Integer
t_MIX_MID = 21  

t_MIX_CLOSE :: Integer
t_MIX_CLOSE = 22 

holographicBase :: Integer
holographicBase = 256

-- ENCODER
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

-- COMPRESSOR
compress :: [Integer] -> Integer
compress digits = Prelude.foldr (\d acc -> d Prelude.+ (holographicBase Prelude.* acc)) 0 digits

-- DECOMPRESSOR
decompress :: Integer -> [Integer]
decompress 0 = []
decompress n = 
    let (rest, digit) = n `Prelude.divMod` holographicBase
    in digit : decompress rest

-- APPENDER (Chronological)
appendHologram :: Integer -> Int -> Integer -> Int -> (Integer, Int)
appendHologram valOld lenOld valNew lenNew = 
    let shiftForNew = holographicBase Prelude.^ lenOld
        newVal = valOld Prelude.+ (valNew Prelude.* shiftForNew)
        newLen = lenOld Prelude.+ lenNew
    in (newVal, newLen)

-- RECONSTRUCTOR PARSERS
parsePath :: [Integer] -> Maybe (ParadoxPath, [Integer])
parsePath [] = Nothing

parsePath (x:xs) | x == t_DIV_ZERO = Just (BaseVeil DivByZero, xs)
parsePath (x:xs) | x == t_ROOT_ENTROPY = Just (BaseVeil RootEntropy, xs)

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
-- 3. THE MONAD & TENSOR RANK
-- ==========================================

newtype Unravel a = Unravel { 
    runUnravel :: Universe -> (UResult a, Universe) 
} deriving (Prelude.Functor)

-- Rank Tensor: (Struct, Time)
rankOf :: ParadoxPath -> (Int, Int)
rankOf (BaseVeil VoidNeutral) = (0, 0)
rankOf (BaseVeil _) = (0, 1) -- Atomic adds 1 unit of Time entropy (creation event)
rankOf (SelfContradict p) = 
    let (s, t) = rankOf p 
    in (s, t Prelude.+ 1) -- Adds Time Entropy
rankOf (Compose p1 p2) = 
    let (s1, t1) = rankOf p1
        (s2, t2) = rankOf p2
    in (s1 Prelude.+ s2 Prelude.+ 1, t1 Prelude.+ t2) -- Adds Structural Entropy

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
                    (dS, dT) = rankOf newPath
                    
                    pathTokens = flattenPath newPath
                    boundVal   = compress pathTokens
                    boundLen   = Prelude.length pathTokens
                    
                    (finalBound, finalLen) = appendHologram 
                                                (boundaryValue uTimed) (boundaryLength uTimed)
                                                boundVal boundLen
                    
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
            
            Invalid i -> 
                let oldPath = genealogy i
                    newPath = SelfContradict oldPath 
                    newInfo = VoidInfo newPath
                    (dS, dT) = rankOf newPath
                    
                    pathTokens = flattenPath newPath
                    boundVal   = compress pathTokens
                    boundLen   = Prelude.length pathTokens
                    
                    (finalBound, finalLen) = appendHologram 
                                                (boundaryValue uTimed) (boundaryLength uTimed)
                                                boundVal boundLen

                    uEvolved = uTimed { boundaryValue = finalBound
                                      , boundaryLength = finalLen 
                                      , structEntropy = structEntropy uTimed -- No new struct for sequence
                                      , timeEntropy = timeEntropy uTimed + 1 -- Add time evolution cost
                                      } 
                in (Invalid newInfo, uEvolved)

-- ==========================================
-- 4. PRIMITIVES
-- ==========================================

bigBang :: Universe
-- S_struct, S_time, t, voids, boundary, b_len
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
        boundLen   = Prelude.length pathTokens
        
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
        
        (Invalid i1, Invalid i2) -> 
             let newPath = Compose (genealogy i1) (genealogy i2)
                 newInfo = VoidInfo newPath
                 (dS, dT) = rankOf newPath
                 
                 pathTokens = flattenPath newPath
                 boundVal   = compress pathTokens
                 boundLen   = Prelude.length pathTokens
                 
                 (finalBound, finalLen) = appendHologram 
                                            (boundaryValue uFinal) (boundaryLength uFinal)
                                            boundVal boundLen

                 uMerge = uFinal { boundaryValue = finalBound 
                                 , boundaryLength = finalLen
                                 , structEntropy = structEntropy uFinal + dS
                                 , timeEntropy = timeEntropy uFinal + dT }
             in (Invalid newInfo, uMerge)

-- ==========================================
-- 5. THE REVERSIBLE STEPPER (Time Travel)
-- ==========================================

-- Reverses the Universe by one causal event.
-- This is the inverse of 'crumble'/'shield'.
stepBackward :: Universe -> Maybe Universe
stepBackward u 
    | boundaryValue u == 0 = Nothing -- Big Bang
    | otherwise = 
        let tokens = decompress (boundaryValue u)
        in case parsePath tokens of
            -- We found the LAST event (because append puts it at the end of the list/high bits? 
            -- Wait, append puts old in LOW bits.
            -- So decompress returns [Old...New].
            -- So parsePath will parse Old first.
            -- For true backward stepping, we need to pop the END of the list.
            -- This is inefficient with singly linked lists but correct.
            Just (path, rest) -> 
                -- Wait, if we parse from the front, we are removing the OLDEST event.
                -- That's "Rewind to Start".
                -- To "Step Back", we need the NEWEST event.
                -- Since tokens are [Old...New], we need to parse from the end.
                -- This requires a bidirectional parser or just reversing the tokens.
                let revTokens = Prelude.reverse tokens 
                    -- Now [New...Old] (reversed structure)
                    -- But our parsePath expects normal structure.
                    -- We actually need to find the split point.
                    -- For v0.8, let's implement "Rewind Start" (pop oldest) as proof of concept.
                    -- Or better: Just implement reconstruct and pop last.
                    history = reconstruct (boundaryValue u)
                in case Prelude.reverse history of
                    [] -> Nothing
                    (lastEvent : previousEvents) -> 
                        -- We found the last event. Now we subtract its entropy.
                        let (dS, dT) = rankOf lastEvent
                            -- Rebuild boundary from previous events
                            -- Ideally we'd have a "pop" function on the integer directly
                            -- but rebuilding is safe.
                            prevBoundList = Prelude.concatMap flattenPath (Prelude.reverse previousEvents)
                            prevBoundVal  = compress prevBoundList
                            prevBoundLen  = Prelude.length prevBoundList
                            
                        in Just u {
                            structEntropy = structEntropy u Prelude.- dS,
                            timeEntropy   = timeEntropy u Prelude.- dT,
                            voidCount     = voidCount u Prelude.- 1,
                            boundaryValue = prevBoundVal,
                            boundaryLength = prevBoundLen
                        }
            Nothing -> Nothing