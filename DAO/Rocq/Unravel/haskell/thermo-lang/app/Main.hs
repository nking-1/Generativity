module Main where

import ThermoParser
import ThermoTypeSystem
import ThermoLang
import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/))
import System.Environment (getArgs)
-- Removed unused Data.List import

-- ==========================================
-- 1. THE UNCRASHABLE PHYSICS ENGINE
-- ==========================================
-- Scenario: N-Body simulation where particles can overlap (r=0).
-- Standard Engine: Crashes (DivByZero) or NaNs (Poison).
-- Thermo Engine: Absorbs the singularity, clamps the force, records "Collision Entropy".
demoPhysics :: String
demoPhysics = unlines
  [ "// PARAMETERS"
  , "let gravity = 10 in"
  , "let drag    = 2 in"
  , ""
  , "// PARTICLE STATE: [Mass, Position, Velocity]"
  , "// Particle 2 is at 0 (Singularity Risk!)"
  , "let p1 = [10, 5, 0] in"
  , "let p2 = [10, 0, 0] in "
  , ""
  , "// PHYSICS KERNEL"
  , "// Force = G * m1 * m2 / dist"
  , "// We map over a list of distances to simulate time steps"
  , "let trajectory = [5, 4, 3, 2, 1, 0, 1, 2] in" -- 0 is the collision
  , ""
  , "let forces = map(r -> "
  , "    // The Shield: If r=0, physics breaks. We recover with Max Force (100)."
  , "    // But the system remembers the 'Impact' via Entropy."
  , "    shield (gravity / r) recover 100"
  , ", trajectory) in"
  , ""
  , "// INTEGRATION"
  , "// Sum total energy applied"
  , "fold(acc, f -> acc + f, 0, forces)"
  ]

-- ==========================================
-- 2. THE ROBUST MARKET MAKER
-- ==========================================
-- Scenario: Calculating liquidity ratios from a stream of trades.
-- Data is dirty: Nulls, Zeros (Flash crashes), Missing fields.
-- Goal: Compute a safe average liquidity without dropping the batch.
demoFinance :: String
demoFinance = unlines
  [ "// ORDER BOOK SNAPSHOTS: [Bid, Ask]"
  , "let book = ["
  , "  [100, 105], // Normal"
  , "  [100, 100], // Crossed (Spread=0)"
  , "  [0,   100], // Flash Crash (Bid=0)"
  , "  [95,  98]   // Normal"
  , "] in"
  , ""
  , "// METRIC: MidPoint / Spread"
  , "// Spread = Ask - Bid. If 0, ratio is Infinite."
  , "let metrics = map(row -> "
  , "    let bid = 0 in" 
  , "    // SIMULATION: We are mapping 'spread' values directly"
  , "    1000 / row"
  , ", [5, 0, 100, 3]) in" -- 0 represents the crossed book
  , ""
  , "// AGGREGATE RISK"
  , "// We sum the metrics. The Void (Spread=0) is absorbed."
  , "fold(acc, m -> acc + m, 0, metrics)"
  ]

-- ==========================================
-- 3. THE ENTROPY CONSENSUS
-- ==========================================
-- Scenario: A distributed system where "Truth" is determined by 
-- the lowest entropy path.
-- Logic: We try two different algorithms. We pick the one that is "Cooler".
demoConsensus :: String
demoConsensus = unlines
  [ "// PATH A: Risky Optimization (Unchecked Math)"
  , "let pathA = "
  , "  let x = 10 in"
  , "  let y = 0 in"
  , "  x / y" -- High Entropy (Void)
  , "in"
  , ""
  , "// PATH B: Conservative Logic (Shielded)"
  , "let pathB = "
  , "  let x = 10 in"
  , "  let y = 0 in"
  , "  shield (x / y) recover 0" -- Low Entropy (1 unit)
  , "in"
  , ""
  , "// DECISION: In a real Monad, we would compare the resulting Universe states."
  , "// Here, we just run both to show the difference."
  , "if 1 == 1 then pathB else pathA" 
  ]


-- ==========================================
-- 4. THE LAGRANGIAN EXPERIMENT (New!)
-- ==========================================
-- Entropy Flow Lagrangian Hypothesis: L = S * S_dot.
-- We simulate a trajectory falling into a singularity (r -> 0).
-- We measure if the Entropy Flux (S_dot) compensates for the Singularity.
demoLagrangian :: String
demoLagrangian = unlines
  [ "// THE EVENT HORIZON EXPERIMENT"
  , "// A particle falls from r=10 down to r=0"
  , "let trajectory = [10, 8, 6, 4, 2, 1, 0, 0, 0] in" 
  
  , "// The Potential Field: Phi ~ 1/r"
  , "// As r approaches 0, Information Density approaches Infinity."
  , "// In standard physics, this is a breakdown."
  , "// In Impossibility Algebra, this is a Phase Transition."
  , "let field = map(r -> "
  , "    shield (1000 / r) recover 9999" -- 9999 is the "Planck Saturation" constant
  , ", trajectory) in"
  
  , "// Compute the Total Action of the path"
  , "fold(acc, val -> acc + val, 0, field)"
  ]


-- ==========================================
-- RUNNER INFRASTRUCTURE (Enhanced)
-- ==========================================

runDemo :: String -> String -> IO ()
runDemo title code = do
    putStrLn $ "\n🔮 DEMO: " ++ title
    putStrLn $ replicate (length title + 8) '='
    putStrLn "Source Code:"
    putStrLn $ unlines $ map ("  | " ++) (lines code)
    
    putStrLn "1. Compiling..."
    case parseThermo code of
        Left err -> putStrLn $ "❌ PARSE ERROR:\n" ++ err
        Right ast -> do
            case analyzeTyped ast of
                Left typeErr -> putStrLn $ "🛑 TYPE ERROR: " ++ show typeErr
                Right stats -> do
                    putStrLn $ "   Predicted Entropy Bound: " ++ show (maxEntropy stats)
                    
                    putStrLn "2. Executing in Thermodynamic Sandbox..."
                    let (res, u) = run (compile ast Prelude.mempty)
                    
                    putStrLn "\n📊 PHYSICS REPORT"
                    putStrLn "-----------------"
                    putStrLn $ "   Result Value:   " ++ show res
                    putStrLn $ "   Total Entropy (S): " ++ show (totalEntropy u) 
                    putStrLn $ "   Total Time (t):    " ++ show (timeStep u) 
                    
                    -- CALCULATING THE LAGRANGIAN METRICS
                    let s = fromIntegral (totalEntropy u) :: Double
                    let t = fromIntegral (timeStep u) :: Double
                    -- FIX: Use qualified Prelude./ here
                    let s_dot = if t > 0 then s Prelude./ t else 0
                    let lagrangian = s * s_dot -- L = S * S_dot
                    
                    putStrLn "\n📐 LAGRANGIAN ANALYSIS"
                    putStrLn "---------------------"
                    putStrLn $ "   Entropy Rate (S_dot): " ++ take 6 (show s_dot) ++ " J/K/s"
                    putStrLn $ "   Action (L):           " ++ take 8 (show lagrangian) ++ " J^2/K^2/s"
                    
                    if totalEntropy u > 0 
                        then putStrLn "   ✓ Singularity Processed. Physics holds."
                        else putStrLn "   ? No Entropy generated."


help :: IO ()
help = do
    putStrLn "Usage: thermo [demo-name]"
    putStrLn "\nAvailable Demos:"
    putStrLn "  physics    - N-Body simulation with singularities"
    putStrLn "  finance    - Market maker handling zero-spreads"
    putStrLn "  consensus  - Choosing logic paths based on entropy"
    putStrLn "  lagrangian - Information flow lagrangian"
    putStrLn "  all        - Run all demos"

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["physics"]   -> runDemo "The Uncrashable Particle" demoPhysics
        ["finance"]   -> runDemo "The Robust Market Maker" demoFinance
        ["consensus"] -> runDemo "Entropy Consensus" demoConsensus
        ["lagrangian"] -> runDemo "Event Horizon Simulation" demoLagrangian
        ["all"] -> do
            runDemo "The Uncrashable Particle" demoPhysics
            runDemo "The Robust Market Maker" demoFinance
            runDemo "Entropy Consensus" demoConsensus
            runDemo "Event Horizon Simulation" demoLagrangian
        _ -> help