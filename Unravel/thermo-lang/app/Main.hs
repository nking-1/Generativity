module Main where

import ThermoParser
import ThermoTypeSystem
import ThermoLang
import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/))
import System.Environment (getArgs)

demoPhysics :: String
demoPhysics = unlines
  [ "// PARAMETERS"
  , "let gravity = 10 in"
  , "let drag    = 2 in"
  , ""
  , "// PARTICLE STATE: [Mass, Position, Velocity]"
  , "let p1 = [10, 5, 0] in"
  , "let p2 = [10, 0, 0] in "
  , ""
  , "// PHYSICS KERNEL"
  , "let trajectory = [5, 4, 3, 2, 1, 0, 1, 2] in"
  , ""
  , "let forces = map(r -> "
  , "    shield (gravity / r) recover 100"
  , ", trajectory) in"
  , ""
  , "fold(acc, f -> acc + f, 0, forces)"
  ]

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
  , "let metrics = map(row -> "
  , "    let bid = 0 in" 
  , "    // SIMULATION: We are mapping 'spread' values directly"
  , "    1000 / row"
  , ", [5, 0, 100, 3]) in" 
  , ""
  , "fold(acc, m -> acc + m, 0, metrics)"
  ]

demoConsensus :: String
demoConsensus = unlines
  [ "// PATH A: Risky Optimization"
  , "let pathA = "
  , "  let x = 10 in"
  , "  let y = 0 in"
  , "  x / y" 
  , "in"
  , ""
  , "// PATH B: Conservative Logic (Shielded)"
  , "let pathB = "
  , "  let x = 10 in"
  , "  let y = 0 in"
  , "  shield (x / y) recover 0"
  , "in"
  , ""
  , "if entropy == 0 then pathA else pathB" 
  ]

demoLagrangian :: String
demoLagrangian = unlines
  [ "// THE EVENT HORIZON EXPERIMENT"
  , "let trajectory = [10, 8, 6, 4, 2, 1, 0, 0, 0] in" 
  , ""
  , "let field = map(r -> "
  , "    shield (1000 / r) recover 9999" 
  , ", trajectory) in"
  , ""
  , "fold(acc, val -> acc + val, 0, field)"
  ]

demoVerifiable :: String
demoVerifiable = unlines
  [ "// DEMO: Verifiable Computation (AdS/CFT)"
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
  , "[clean_run, shielded_run]"
  ]

demoTimeMachine :: String
demoTimeMachine = unlines
  [ "// DEMO: The Time Machine (Structure Reconstruction)"
  , "// We create a nested failure structure."
  , ""
  , "// 1. A simple singularity"
  , "let s1 = shield (1/0) recover 0 in"
  , ""
  , "// 2. A nested recovery (Branching)"
  , "let s2 = shield ("
  , "    shield (1/0) recover 0" 
  , ") recover 0 in"
  , ""
  , "// Result is irrelevant, we want the Hologram."
  , "[s1, s2, hologram]"
  ]

printPath :: String -> ParadoxPath -> IO ()
printPath indent p = case p of
    BaseVeil src -> putStrLn $ indent ++ "💥 " ++ show src
    SelfContradict next -> do
        putStrLn $ indent ++ "⏳ Time Step (Next) ->"
        printPath (indent ++ "  ") next
    Compose p1 p2 -> do
        putStrLn $ indent ++ "🔀 Entangled Branch {"
        printPath (indent ++ "  L: ") p1
        printPath (indent ++ "  R: ") p2
        putStrLn $ indent ++ "}"

runAnalysis :: ProgramStats -> IO ()
runAnalysis stats = do
    let s = fromIntegral (maxEntropy stats) :: Double
    let t = fromIntegral (timeCost stats) :: Double
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
    putStrLn $ "   Entropy Tensor:  " ++ "[Struct=" ++ show (structEntropy u) ++ ", Time=" ++ show (timeEntropy u) ++ "]"
    putStrLn $ "   Total Entropy:   " ++ show (totalEntropy u)
    putStrLn $ "   Work Done (Mass):" ++ show (mass u)
    putStrLn $ "   Total Time (t):  " ++ show (timeStep u) 
    putStrLn $ "   Holographic Sig: " ++ show (boundaryValue u)

    -- RECONSTRUCTION
    putStrLn "\n🕰️  HOLOGRAPHIC RECONSTRUCTION (Time Machine)"
    putStrLn "-------------------------------------------"
    let history = reconstruct (boundaryValue u)
    if null history
        then putStrLn "   (Vacuum State / No Singularities)"
        else do
            putStrLn $ "   Found " ++ show (length history) ++ " distinct causal events:"
            mapM_ (\p -> do
                putStrLn "   --- EVENT ---"
                printPath "   " p
                ) history

    -- LAGRANGIAN
    let s = fromIntegral (totalEntropy u) :: Double
    let t = fromIntegral (timeStep u) :: Double
    let s_dot = if t > 0 then s Prelude./ t else 0
    
    let s_ddot = if t > 0 then s_dot Prelude./ t else 0
    let lagrangian = s * s_dot 
    
    putStrLn "\n📐 LAGRANGIAN ANALYSIS"
    putStrLn "---------------------"
    putStrLn $ "   Entropy Rate (S_dot): " ++ take 6 (show s_dot) ++ " J/K/s"
    putStrLn $ "   Accel (S_ddot):       " ++ take 6 (show s_ddot) ++ " J/K/s^2"
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
                    case build ast of
                        Rejected reason -> putStrLn $ "❌ REJECTED: " ++ reason
                        Accepted _ prog -> do
                            runAnalysis stats
                            runExecution prog

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
    putStrLn "  timemachine  - Demo of structural reconstruction"
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
        ["timemachine"] -> runDemo "The Time Machine" demoTimeMachine
        ["all"] -> do
            runDemo "The Uncrashable Particle" demoPhysics
            runDemo "The Robust Market Maker" demoFinance
            runDemo "Entropy Consensus" demoConsensus
            runDemo "Event Horizon Simulation" demoLagrangian
            runDemo "Holographic Verification" demoVerifiable
            runDemo "The Time Machine" demoTimeMachine

        ["run", path] -> runFile path

        _ -> help