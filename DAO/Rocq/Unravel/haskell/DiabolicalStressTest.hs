-- DiabolicalStressTest.hs
-- Comprehensive stress testing of the formal Haskell Unravel reference
-- Using the actual Unravel library to match our TypeScript testing patterns

import Unravel
import Prelude hiding (lookup)
import Control.Monad (when)

-- Helper to show thermodynamic results
showThermo :: Prod ValueT Universe -> String
showThermo (Pair v u) = 
  "entropy=" ++ show (total_entropy u) ++ 
  ", time=" ++ show (time_step u) ++ 
  ", voids=" ++ show (void_count u)

-- Extract entropy for analysis
getEntropy :: ExprV -> Integer
getEntropy expr = case run_thermo expr of
  Pair _ u -> total_entropy u

-- Extract time for analysis  
getTime :: ExprV -> Integer
getTime expr = case run_thermo expr of
  Pair _ u -> time_step u

-- Extract void count
getVoidCount :: ExprV -> Integer
getVoidCount expr = case run_thermo expr of
  Pair _ u -> void_count u

-- ============================================================================
-- ENTROPY BOMB TEST (Matching TypeScript Pattern)
-- ============================================================================

-- Create entropy bomb exactly like TypeScript version
entropyBomb :: Integer -> ExprV
entropyBomb 0 = EVDiv (EVNum 1) (EVNum 0)
entropyBomb n = EVAdd (entropyBomb (n-1)) (entropyBomb (n-1))

testEntropyBombReference :: IO ()
testEntropyBombReference = do
  putStrLn "💥 ENTROPY BOMB TEST ON HASKELL REFERENCE"
  putStrLn "Testing the exact pattern that caused time anomalies in TypeScript...\n"
  
  putStrLn "Entropy bomb progression:"
  mapM_ (\depth -> do
    let expr = entropyBomb depth
    let result = run_thermo expr
    case result of
      Pair v u -> do
        putStrLn $ "  Bomb " ++ show depth ++ ": " ++ showThermo result
        
        -- Check for time evolution anomalies
        when (depth > 0) $ do
          let prevResult = run_thermo (entropyBomb (depth-1))
          case prevResult of
            Pair _ prevU -> do
              let timeDiff = time_step u - time_step prevU
              let entropyDiff = total_entropy u - total_entropy prevU
              
              when (timeDiff == 0 && entropyDiff > 0) $
                putStrLn $ "    🚨 TIME ANOMALY: entropy increased but time didn't advance"
              
              when (time_step u == time_step prevU && depth > 5) $
                putStrLn $ "    🤔 TIME STAGNATION: same time as previous depth"
    ) [0..12]  -- Test same range as TypeScript

-- ============================================================================  
-- MATHEMATICAL LAW STRESS TEST
-- ============================================================================

testMathematicalLawsReference :: IO ()
testMathematicalLawsReference = do
  putStrLn "\n🧮 MATHEMATICAL LAW STRESS TEST ON REFERENCE"
  putStrLn "Testing Noether's theorem and conservation laws systematically...\n"
  
  -- Test Noether's theorem with many cases
  putStrLn "Testing Noether's theorem (commutativity):"
  let noetherTests = [(a, b) | a <- [1..100], b <- [1..100]]
  let noetherResults = map (\(a, b) -> 
        getEntropy (EVAdd (EVNum a) (EVNum b)) == 
        getEntropy (EVAdd (EVNum b) (EVNum a))) noetherTests
  
  let noetherViolations = length (filter not noetherResults)
  let noetherTotal = length noetherResults
  
  putStrLn $ "  Tests: " ++ show noetherTotal
  putStrLn $ "  Violations: " ++ show noetherViolations
  putStrLn $ "  Success rate: " ++ show (fromIntegral (noetherTotal - noetherViolations) / fromIntegral noetherTotal * 100) ++ "%"
  
  when (noetherViolations > 0) $
    putStrLn "  🚨 NOETHER VIOLATIONS IN REFERENCE IMPLEMENTATION!"
  
  -- Test conservation laws
  putStrLn "\nTesting conservation laws (recovery preserves entropy):"
  let conservationTests = [1..1000]
  let conservationResults = map (\n ->
        let voidExpr = EVDiv (EVNum n) (EVNum 0)
            recoveredExpr = EVDefault voidExpr (EVNum 999)
            voidEntropy = getEntropy voidExpr
            recoveredEntropy = getEntropy recoveredExpr
        in voidEntropy == recoveredEntropy) conservationTests
  
  let conservationViolations = length (filter not conservationResults)
  let conservationTotal = length conservationResults
  
  putStrLn $ "  Tests: " ++ show conservationTotal
  putStrLn $ "  Violations: " ++ show conservationViolations  
  putStrLn $ "  Success rate: " ++ show (fromIntegral (conservationTotal - conservationViolations) / fromIntegral conservationTotal * 100) ++ "%"

-- ============================================================================
-- TIME EVOLUTION INVESTIGATION
-- ============================================================================

investigateTimeEvolutionReference :: IO ()
investigateTimeEvolutionReference = do
  putStrLn "\n⏰ TIME EVOLUTION INVESTIGATION ON REFERENCE"
  putStrLn "Investigating time advancement patterns in formal implementation...\n"
  
  -- Test progressive void creation
  let voidProgression = [
        ("Single void", EVDiv (EVNum 1) (EVNum 0)),
        ("Double void", EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVDiv (EVNum 2) (EVNum 0))),
        ("Triple void", EVAdd (EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVDiv (EVNum 2) (EVNum 0))) (EVDiv (EVNum 3) (EVNum 0))),
        ("Void cascade", EVAdd (EVDiv (EVNum 100) (EVNum 0)) (EVAdd (EVVar "undefined") (EVMod (EVNum 50) (EVNum 0)))),
        ("Complex chain", EVLet "x" (EVDiv (EVNum 10) (EVNum 0)) 
                                (EVLet "y" (EVAdd (EVVar "x") (EVVar "missing"))
                                  (EVAdd (EVVar "x") (EVVar "y"))))]
  
  putStrLn "Time evolution in void progression:"
  mapM_ (\(name, expr) -> do
    let Pair v u = run_thermo expr
    putStrLn $ "  " ++ name ++ ": " ++ showThermo (Pair v u)
    
    -- Detailed analysis
    case v of
      VTVoid (VInfo e t s) -> putStrLn $ "    Void info: entropy=" ++ show e ++ ", failure_time=" ++ show t
      _ -> return ()
    ) voidProgression

-- ============================================================================
-- COMPARISON TEST (TypeScript vs Haskell)
-- ============================================================================

compareTypeScriptBehavior :: IO ()
compareTypeScriptBehavior = do
  putStrLn "\n🆚 COMPARISON: REFERENCE vs TYPESCRIPT BEHAVIOR"
  putStrLn "Testing exact cases that showed anomalies in TypeScript...\n"
  
  -- Cases that caused time stagnation in TypeScript
  let problematicCases = [
        ("TS Complexity 8", entropyBomb 8),
        ("TS Complexity 10", entropyBomb 10),
        ("TS High entropy", foldl1 EVAdd [EVDiv (EVNum n) (EVNum 0) | n <- [1..20]])]
  
  putStrLn "Testing TypeScript problematic cases on Haskell reference:"
  mapM_ (\(name, expr) -> do
    let Pair v u = run_thermo expr
    putStrLn $ "  " ++ name ++ ": " ++ showThermo (Pair v u)
    
    -- Check if reference shows same issues
    when (total_entropy u > 1000 && time_step u < void_count u) $
      putStrLn $ "    🚨 REFERENCE ALSO SHOWS TIME ISSUE"
    
    when (total_entropy u > 1000 && time_step u >= void_count u) $
      putStrLn $ "    ✅ REFERENCE HANDLES HIGH ENTROPY CORRECTLY"
    ) problematicCases

-- ============================================================================
-- FUEL MECHANISM STRESS TEST
-- ============================================================================

testFuelMechanismReference :: IO ()
testFuelMechanismReference = do
  putStrLn "\n⛽ FUEL MECHANISM STRESS TEST ON REFERENCE"
  putStrLn "Testing fuel exhaustion patterns...\n"
  
  -- Test expressions with different fuel requirements
  let fuelTests = [
        ("Simple", EVAdd (EVNum 1) (EVNum 2)),
        ("Medium complexity", EVAdd (EVAdd (EVNum 1) (EVNum 2)) (EVAdd (EVNum 3) (EVNum 4))),
        ("High complexity", foldl1 EVAdd [EVNum n | n <- [1..100]]),
        ("Exponential", massiveNesting 15),
        ("Deep nesting", deepLetNesting 50)
        ]
  
  putStrLn "Fuel consumption analysis:"
  mapM_ (\(name, expr) -> do
    let Pair v u = run_thermo expr
    putStrLn $ "  " ++ name ++ ": " ++ showValue v
    
    -- Report entropy generation from evaluation
    putStrLn $ "    Entropy: " ++ show (total_entropy u) ++ ", Time: " ++ show (time_step u)
    ) fuelTests

-- Helper to display values
showValue :: ValueT -> String
showValue (VTNum n) = "Num(" ++ show n ++ ")"
showValue (VTBool b) = "Bool(" ++ show b ++ ")"
showValue (VTVoid (VInfo e t s)) = "Void(entropy=" ++ show e ++ ")"

-- Helper functions matching the stress test patterns
massiveNesting :: Integer -> ExprV
massiveNesting 0 = EVNum 1
massiveNesting n = EVAdd (massiveNesting (n-1)) (massiveNesting (n-1))

deepLetNesting :: Integer -> ExprV  
deepLetNesting 0 = EVNum 42
deepLetNesting n = 
  EVLet ("x" ++ show n) (EVNum n)
    (EVAdd (EVVar ("x" ++ show n)) (deepLetNesting (n-1)))

-- ============================================================================
-- MAIN EXECUTION
-- ============================================================================

main :: IO ()
main = do
  putStrLn "😈 DIABOLICAL STRESS TEST OF HASKELL REFERENCE IMPLEMENTATION"
  
  testEntropyBombReference
  testMathematicalLawsReference
  investigateTimeEvolutionReference
  compareTypeScriptBehavior
  testFuelMechanismReference
  
  putStrLn "\n🏆 HASKELL REFERENCE STRESS TEST COMPLETE"