module Main where

import ThermoParser
import ThermoTypeSystem
import ThermoLang
import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/))
import System.Environment (getArgs)

-- ==========================================
-- 1. THE UNCRASHABLE PHYSICS ENGINE
-- ==========================================
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
  , "let trajectory = [5, 4, 3, 2, 1, 0, 1, 2] in" -- 0 is the collision
  , ""
  , "let forces = map(r -> "
  , "    // The Shield: If r=0, physics breaks. We recover with Max Force (100)."
  , "    shield (gravity / r) recover 100"
  , ", trajectory) in"
  , ""
  , "// INTEGRATION"
  , "fold(acc, f -> acc + f, 0, forces)"
  ]

-- ==========================================
-- 2. THE ROBUST MARKET MAKER
-- ==========================================
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
  , "let metrics = map(row -> "
  , "    let bid = 0 in" 
  , "    // SIMULATION: We are mapping 'spread' values directly"
  , "    1000 / row"
  , ", [5, 0, 100, 3]) in" -- 0 represents the crossed book
  , ""
  , "// AGGREGATE RISK"
  , "fold(acc, m -> acc + m, 0, metrics)"
  ]

-- ==========================================
-- 3. THE ENTROPY CONSENSUS
-- ==========================================
demoConsensus :: String
demoConsensus = unlines
  [ "// PATH A: Risky Optimization"
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
  , "// DECISION: In v0.4 we can check the entropy directly!"
  , "if entropy == 0 then pathA else pathB" 
  ]

-- ==========================================
-- 4. THE LAGRANGIAN EXPERIMENT
-- ==========================================
demoLagrangian :: String
demoLagrangian = unlines
  [ "// THE EVENT HORIZON EXPERIMENT"
  , "let trajectory = [10, 8, 6, 4, 2, 1, 0, 0, 0] in" 
  , ""
  , "// The Potential Field: Phi ~ 1/r"
  , "let field = map(r -> "
  , "    shield (1000 / r) recover 9999" -- 9999 is the "Planck Saturation" constant
  , ", trajectory) in"
  , ""
  , "// Compute the Total Action of the path"
  , "fold(acc, val -> acc + val, 0, field)"
  ]

-- ==========================================
-- 5. VERIFIABLE COMPUTATION (Holography)
-- ==========================================
demoVerifiable :: String
demoVerifiable = unlines
  [ "// DEMO: Verifiable Computation (AdS/CFT)"
  , "// We produce the same result value (100) via two different realities."
  , "// The Hologram proves which reality we inhabited."
  , ""
  , "// Reality 1: The Clean Path (100 / 1)"
  , "let clean_run = "
  , "    let val = 100 / 1 in"
  , "    [val, hologram] "
  , "in"
  , ""
  , "// Reality 2: The Shielded Path (100 / 0 -> Recover)"
  , "let shielded_run = "
  , "    let val = shield (100 / 0) recover 100 in"
  , "    [val, hologram]"
  , "in"
  , ""
  , "// Return both to compare signatures."
  , "// Result: [ [100, 0], [100, <Hash>] ]"
  , "[clean_run, shielded_run]"
  ]

-- ==========================================
-- RUNNER INFRASTRUCTURE (The Static Optimizer)
-- ==========================================

runAnalysis :: ProgramStats -> IO ()
runAnalysis stats = do
    let s = fromIntegral (maxEntropy stats) :: Double
    let t = fromIntegral (timeCost stats) :: Double
    -- Action = S * (S_dot) = S * (S/t)
    let action = if t > 0 then s * (s Prelude./ t) else 0
    
    putStrLn $ "   Predicted Entropy: " ++ show (maxEntropy stats)
    putStrLn $ "   Predicted Cost:    " ++ show (timeCost stats)
    putStrLn $ "   Predicted Action:  " ++ take 6 (show action)
    
    if action > 50.0 
        then putStrLn "⚠️  WARNING: High Thermodynamic Cost. Renormalization Recommended."
        else putStrLn "✓  Action within stability limits."

runExecution :: Unravel UVal -> IO ()
runExecution prog = do
    putStrLn "2. Executing in Thermodynamic Sandbox..."
    let (res, u) = run prog
    
    putStrLn "\n📊 PHYSICS REPORT"
    putStrLn "-----------------"
    putStrLn $ "   Result Value:    " ++ show res
    putStrLn $ "   Total Entropy (S): " ++ show (totalEntropy u) 
    putStrLn $ "   Total Time (t):    " ++ show (timeStep u) 
    
    -- Holographic Output
    putStrLn $ "   Holographic Sig:   " ++ show (boundaryHash u)

    -- Runtime Lagrangian
    let s = fromIntegral (totalEntropy u) :: Double
    let t = fromIntegral (timeStep u) :: Double
    let s_dot = if t > 0 then s Prelude./ t else 0
    let lagrangian = s * s_dot 
    
    putStrLn "\n📐 LAGRANGIAN ANALYSIS"
    putStrLn "---------------------"
    putStrLn $ "   Entropy Rate (S_dot): " ++ take 6 (show s_dot) ++ " J/K/s"
    putStrLn $ "   Action (L):           " ++ take 8 (show lagrangian) ++ " J^2/K^2/s"
    
    if totalEntropy u > 0 
        then putStrLn "   ✓ Singularity Processed. Physics holds."
        else putStrLn "   ? No Entropy generated."

runDemo :: String -> String -> IO ()
runDemo title code = do
    putStrLn $ "\n🔮 DEMO: " ++ title
    putStrLn $ replicate (length title + 8) '='
    putStrLn "Source Code:"
    putStrLn $ unlines $ map ("  | " ++) (lines code)
    
    putStrLn "1. Compiling & Optimizing..."
    case parseThermo code of
        Left err -> putStrLn $ "❌ PARSE ERROR:\n" ++ err
        Right ast -> do
            case analyzeTyped ast of
                Left typeErr -> putStrLn $ "🛑 TYPE ERROR: " ++ show typeErr
                Right stats -> do
                    runAnalysis stats
                    runExecution (compile ast Prelude.mempty)

runFile :: FilePath -> IO ()
runFile path = do
    putStrLn $ "\n📄 Loading script: " ++ path
    exists <- Prelude.readFile path

    putStrLn "1. Compiling & Optimizing..."
    case parseThermo exists of
        Left err -> putStrLn $ "❌ PARSE ERROR:\n" ++ err
        Right ast -> do
            case analyzeTyped ast of
                Left typeErr -> putStrLn $ "🛑 TYPE ERROR: " ++ show typeErr
                Right stats -> do
                    runAnalysis stats
                    runExecution (compile ast Prelude.mempty)

help :: IO ()
help = do
    putStrLn "Usage: thermo [demo-name]"
    putStrLn "\nAvailable Commands:"
    putStrLn "  physics      - N-Body simulation with singularities"
    putStrLn "  finance      - Market maker handling zero-spreads"
    putStrLn "  consensus    - Choosing logic paths based on entropy"
    putStrLn "  lagrangian   - Information flow Lagrangian"
    putStrLn "  verifiable   - Holographic proof of computation"
    putStrLn "  all          - Run all demos"
    putStrLn "  run <file>   - Run a .thermo script from disk"

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["physics"]    -> runDemo "The Uncrashable Particle" demoPhysics
        ["finance"]    -> runDemo "The Robust Market Maker" demoFinance
        ["consensus"]  -> runDemo "Entropy Consensus" demoConsensus
        ["lagrangian"] -> runDemo "Event Horizon Simulation" demoLagrangian
        ["verifiable"] -> runDemo "Holographic Verification" demoVerifiable
        ["all"] -> do
            runDemo "The Uncrashable Particle" demoPhysics
            runDemo "The Robust Market Maker" demoFinance
            runDemo "Entropy Consensus" demoConsensus
            runDemo "Event Horizon Simulation" demoLagrangian
            runDemo "Holographic Verification" demoVerifiable

        ["run", path] -> runFile path

        _ -> help