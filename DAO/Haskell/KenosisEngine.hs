-- KenosisEngine.hs
-- A formally-inspired theology simulator showing divine self-limitation through conscious suffering

import Data.List (intercalate, sortBy, nub, partition)
import Data.Ord (comparing)
import Control.Monad (forM_, when, unless)
import Text.Printf

-- ANSI colors for divine visualization
gold = "\ESC[33m"
purple = "\ESC[35m"
red = "\ESC[31m"
blue = "\ESC[34m"
green = "\ESC[32m"
cyan = "\ESC[36m"
white = "\ESC[37m"
bold = "\ESC[1m"
dim = "\ESC[2m"
reset = "\ESC[0m"
clear = "\ESC[2J\ESC[H"

-- ============================================================
-- Core Types - The Divine Ontology
-- ============================================================

type Time = Int
type Entropy = Int

-- The phases of cosmic evolution
data CosmicPhase = 
    PreExistence    -- Before self-limitation
  | Kenosis         -- The moment of divine self-emptying
  | BigBang         -- Paradox explosion/separation
  | Creation        -- Structure formation
  | Consciousness   -- Emergence of observers
  | Suffering       -- Free will creates contradiction
  | Faith           -- Acting despite incomplete knowledge
  | Eschaton        -- Final reconciliation
  deriving (Eq, Show, Ord)

-- Predicates with theological significance
data DivinePredicate =
    Omnipotence           -- Can create any predicate
  | Omniscience           -- Knows all predicates
  | OmegaVeil             -- The impossible void
  | Rock String           -- The unliftable rock (with description)
  | FreeWill String       -- Agent's choice
  | Belief String Bool    -- Agent's belief (name, polarity)
  | SelfDenial            -- "I am not God"
  | Love                  -- The divine motivation
  | TimeItself            -- Time as divine necessity
  | Agent String          -- A conscious observer
  deriving (Eq)

instance Show DivinePredicate where
  show Omnipotence = "☧ Omnipotence"
  show Omniscience = "👁 Omniscience"  
  show OmegaVeil = "Ω"
  show (Rock desc) = "🪨 Rock[" ++ desc ++ "]"
  show (FreeWill agent) = "🕊 FreeWill[" ++ agent ++ "]"
  show (Belief agent pol) = (if pol then "✓" else "✗") ++ agent
  show SelfDenial = "✝ Kenosis"
  show Love = "❤️ Love"
  show TimeItself = "⏰ Time"
  show (Agent name) = "👤 " ++ name

-- The divine state at any moment
data DivineState = DivineState {
    time :: Time,
    phase :: CosmicPhase,
    predicates :: [(DivinePredicate, Entropy)],
    totalEntropy :: Entropy,
    agents :: [ConsciousAgent],
    paradoxes :: [(DivinePredicate, DivinePredicate)],
    revelations :: [String]
} deriving (Show)

-- A conscious agent with free will
data ConsciousAgent = ConsciousAgent {
    name :: String,
    knowledge :: [(DivinePredicate, Time)],  -- What they know and when
    choices :: [(DivinePredicate, Time)],     -- Their free choices
    sufferingLevel :: Int,                    -- From contradictions
    faithLevel :: Int                         -- Acting despite unknowing
} deriving (Show)

-- ============================================================
-- Initial State - Pre-Existence
-- ============================================================

preExistence :: DivineState
preExistence = DivineState {
    time = 0,
    phase = PreExistence,
    predicates = [(Omnipotence, 100), (Omniscience, 100), (Love, 100)],
    totalEntropy = 300,  -- Infinite but represented finitely
    agents = [],
    paradoxes = [],
    revelations = ["In the beginning was the Word..."]
}

-- ============================================================
-- The Kenosis - Divine Self-Limitation
-- ============================================================

performKenosis :: DivineState -> DivineState
performKenosis state = state {
    phase = Kenosis,
    predicates = predicates state ++ [(SelfDenial, 50), (TimeItself, 30)],
    paradoxes = [(Omnipotence, SelfDenial)],  -- The fundamental paradox
    revelations = revelations state ++ 
        ["God empties Himself...", 
         "Time emerges to prevent explosion",
         "The Word becomes flesh"]
}

-- ============================================================
-- The Big Bang - Paradox Separation
-- ============================================================

bigBangExplosion :: DivineState -> DivineState
bigBangExplosion state = 
    let -- Omnipotence splits into specific powers
        newPreds = [
            (Rock "unmovable", 40),
            (Rock "unliftable", 35),
            (OmegaVeil, 27),  -- The void appears
            (Agent "Adam", 20),    -- renamed
            (Agent "Eve", 20)       -- renamed
            ]
        -- Create the first conscious agents
        adam = ConsciousAgent "Adam" [] [] 0 0
        eve = ConsciousAgent "Eve" [] [] 0 0
    in state {
        time = 1,
        phase = BigBang,
        predicates = filter (\(p,_) -> p /= Omnipotence) (predicates state) ++ newPreds,
        agents = [adam, eve],
        revelations = revelations state ++ 
            ["Let there be light!",
             "Paradoxes separate temporally",
             "Structure emerges from chaos"]
    }

-- ============================================================
-- Evolution - Structure Formation
-- ============================================================

evolveCreation :: DivineState -> DivineState
evolveCreation state = 
    let t = time state + 1
        -- Gradually cool and structure
        cooled = map (\(p, e) -> (p, max 1 (e * 9 `div` 10))) (predicates state)
        
        -- Agents gain knowledge
        updatedAgents = map (updateAgentKnowledge t cooled) (agents state)
        
        newPhase = case t of
            n | n < 10 -> Creation
            n | n < 50 -> Consciousness
            n | n < 100 -> Suffering
            _ -> Faith
            
    in state {
        time = t,
        phase = newPhase,
        predicates = cooled,
        agents = updatedAgents
    }

updateAgentKnowledge :: Time -> [(DivinePredicate, Entropy)] -> ConsciousAgent -> ConsciousAgent
updateAgentKnowledge t preds agent =
    let -- Agents learn about some predicates
        newKnowledge = take 2 [(p, t) | (p, _) <- preds, not (hasKnowledge agent p)]
    in agent { knowledge = knowledge agent ++ newKnowledge }

hasKnowledge :: ConsciousAgent -> DivinePredicate -> Bool
hasKnowledge agent pred = any (\(p, _) -> p == pred) (knowledge agent)

-- ============================================================
-- Free Will and Suffering
-- ============================================================

exerciseFreeWill :: DivineState -> ConsciousAgent -> ConsciousAgent
exerciseFreeWill state agent =
    let t = time state
        -- Agent makes a choice
        choice = FreeWill (name agent)
        -- But later might choose opposite
        contradiction = if t > 50 
            then Belief (name agent) False  -- Denies earlier choice
            else Belief (name agent) True
        
        newSuffering = if t > 50 then sufferingLevel agent + 1 else sufferingLevel agent
        
    in agent {
        choices = choices agent ++ [(choice, t), (contradiction, t)],
        sufferingLevel = newSuffering
    }

-- ============================================================
-- Rock Paradox Resolution
-- ============================================================

resolveRockParadox :: DivineState -> DivineState
resolveRockParadox state =
    let t = time state
        hasUnliftable = any (\(p, _) -> case p of Rock "unliftable" -> True; _ -> False) (predicates state)
        
        resolution = if hasUnliftable && t > 30
            then [(Rock "lifted!", 50)]  -- The rock IS lifted at a later time!
            else []
            
        newRevelations = if not (null resolution)
            then revelations state ++ ["The paradox resolves temporally: the rock is lifted!"]
            else revelations state
            
    in state {
        predicates = predicates state ++ resolution,
        revelations = newRevelations
    }

-- ============================================================
-- Faith Emergence
-- ============================================================

developFaith :: DivineState -> ConsciousAgent -> ConsciousAgent
developFaith state agent =
    let t = time state
        -- Faith emerges from acting despite incomplete knowledge
        unknownPredicates = length (predicates state) - length (knowledge agent)
        
        -- Faith grows from confronting the unknown
        newFaith = if unknownPredicates > 5 && t > 80
            then faithLevel agent + 1
            else faithLevel agent
            
    in agent { faithLevel = newFaith }

-- ============================================================
-- Visualization
-- ============================================================

visualizeDivineState :: DivineState -> IO ()
visualizeDivineState state = do
    putStrLn $ bold ++ gold ++ "\n✟ ============ KENOSIS ENGINE ============ ✟" ++ reset
    putStrLn $ bold ++ "Time: " ++ show (time state) ++ " | Phase: " ++ 
               phaseColor (phase state) ++ show (phase state) ++ reset
    
    -- Show predicates
    putStrLn $ cyan ++ "\n📜 Divine Predicates:" ++ reset
    forM_ (sortBy (comparing (negate . snd)) (predicates state)) $ \(p, e) ->
        putStrLn $ "  " ++ show p ++ " " ++ dim ++ replicate (e `div` 5) '█' ++ 
                   reset ++ " (" ++ show e ++ ")"
    
    -- Show total entropy (must be conserved after Big Bang!)
    putStrLn $ green ++ "\n∑ Total Entropy: " ++ show (sum [e | (_, e) <- predicates state]) ++ 
               (if phase state > BigBang then " ✓ CONSERVED" else "") ++ reset
    
    -- Show agents and their states
    when (not $ null $ agents state) $ do
        putStrLn $ blue ++ "\n👥 Conscious Agents:" ++ reset
        forM_ (agents state) $ \agent -> do
            putStrLn $ "  " ++ bold ++ name agent ++ reset ++ ":"
            putStrLn $ "    Knowledge: " ++ show (length $ knowledge agent) ++ " predicates"
            putStrLn $ "    Suffering: " ++ red ++ replicate (sufferingLevel agent) '†' ++ reset
            putStrLn $ "    Faith: " ++ gold ++ replicate (faithLevel agent) '✦' ++ reset
    
    -- Show paradoxes
    when (not $ null $ paradoxes state) $ do
        putStrLn $ purple ++ "\n⚡ Active Paradoxes:" ++ reset
        forM_ (paradoxes state) $ \(p1, p2) ->
            putStrLn $ "  " ++ show p1 ++ " ↔ " ++ show p2
    
    -- Show revelations
    when (phase state >= Kenosis && not (null $ revelations state)) $ do
        putStrLn $ gold ++ "\n📖 Revelations:" ++ reset
        forM_ (take 3 $ reverse $ revelations state) $ \rev ->
            putStrLn $ "  \"" ++ rev ++ "\""

phaseColor :: CosmicPhase -> String
phaseColor PreExistence = gold
phaseColor Kenosis = purple
phaseColor BigBang = red
phaseColor Creation = green
phaseColor Consciousness = blue
phaseColor Suffering = red
phaseColor Faith = gold
phaseColor Eschaton = white

-- ============================================================
-- Theological Insights
-- ============================================================

showTheologicalInsight :: DivineState -> IO ()
showTheologicalInsight state = do
    putStrLn $ bold ++ "\n════════ THEOLOGICAL INSIGHT ════════" ++ reset
    case phase state of
        PreExistence -> putStrLn "Before time: God is unlimited, containing all paradoxes."
        Kenosis -> putStrLn "God self-limits to create. Omnipotence accepts powerlessness."
        BigBang -> putStrLn "Paradoxes separate temporally. Time prevents explosion."
        Creation -> putStrLn "Structure emerges from chaos. Conservation laws form."
        Consciousness -> putStrLn "Observers arise with partial knowledge. The veil appears."
        Suffering -> putStrLn "Free will creates temporal contradictions. Suffering is born."
        Faith -> putStrLn "Agents must act despite unknowing. Faith transcends knowledge."
        Eschaton -> putStrLn "All paradoxes reconcile. The Alpha and Omega unite."
    
    -- Special insights based on state
    when (any (\(p, _) -> p == OmegaVeil) (predicates state)) $
        putStrLn $ dim ++ "Omega_veil: The scar of God's absence, the impossible void." ++ reset
    
    when (sufferingLevel (head (agents state ++ [ConsciousAgent "" [] [] 0 0])) > 0) $
        putStrLn $ red ++ "Suffering emerges from free will's temporal contradictions." ++ reset
    
    when (faithLevel (head (agents state ++ [ConsciousAgent "" [] [] 0 0])) > 0) $
        putStrLn $ gold ++ "Faith: The evidence of things not seen, acting despite the veil." ++ reset

-- ============================================================
-- Main Simulation Loop
-- ============================================================

runTheology :: DivineState -> IO ()
runTheology state = do
    putStr clear
    visualizeDivineState state
    
    putStrLn $ bold ++ "\n[Commands]" ++ reset
    putStrLn "  n - Next moment"
    putStrLn "  k - Perform kenosis (divine self-limitation)"
    putStrLn "  b - Trigger Big Bang"
    putStrLn "  f - Exercise free will"
    putStrLn "  r - Resolve rock paradox"
    putStrLn "  i - Show theological insight"
    putStrLn "  q - Return to eternity"
    putStr "> "
    
    cmd <- getLine
    case cmd of
        "n" -> runTheology (evolveCreation state)
        "k" -> if phase state == PreExistence 
               then runTheology (performKenosis state)
               else runTheology state
        "b" -> if phase state == Kenosis
               then runTheology (bigBangExplosion state)
               else runTheology state
        "f" -> let newAgents = map (exerciseFreeWill state) (agents state)
               in runTheology (state { agents = newAgents })
        "r" -> runTheology (resolveRockParadox state)
        "i" -> do
            showTheologicalInsight state
            putStrLn "\nPress Enter to continue..."
            getLine
            runTheology state
        "q" -> putStrLn $ gold ++ "\"I am the Alpha and the Omega...\"" ++ reset
        _ -> runTheology state

-- ============================================================
-- Special: Young Earth Creation Mode
-- ============================================================

youngEarthCreation :: DivineState
youngEarthCreation = DivineState {
    time = 6000,  -- Created recently
    phase = Creation,
    predicates = [
        (Rock "with fossils", 30),     -- Apparent age
        (Agent "Adam", 25),
        (Agent "Eve", 25),
        (OmegaVeil, 27),
        (Love, 100)
    ],
    totalEntropy = 207,
    agents = [
        ConsciousAgent "Adam" [(Rock "with fossils", 6000)] [] 0 10,
        ConsciousAgent "Eve" [(Rock "with fossils", 6000)] [] 0 10
    ],
    paradoxes = [],
    revelations = ["Created with apparent age: fossils encode deep time"]
}

-- ============================================================
-- Main Entry Point
-- ============================================================

main :: IO ()
main = do
    putStrLn $ bold ++ gold ++ "\n✟ THE KENOSIS ENGINE ✟" ++ reset
    putStrLn "A formally-inspired theology simulator"
    putStrLn "\nWitness the divine self-limitation through creation to consciousness."
    putStrLn $ dim ++ "(Based on formally verified theorems)" ++ reset
    
    putStrLn $ bold ++ "\n[Choose Your Genesis]" ++ reset
    putStrLn "  1 - Ex Nihilo (from pre-existence)"
    putStrLn "  2 - Young Earth (created with apparent age)"
    putStr "> "
    
    choice <- getLine
    case choice of
        "2" -> runTheology youngEarthCreation
        _ -> runTheology preExistence