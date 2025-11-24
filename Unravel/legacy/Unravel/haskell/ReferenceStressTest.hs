-- ReferenceStressTest.hs
-- Simple but comprehensive stress test of Haskell reference
-- Using actual Unravel library to validate TypeScript implementation

import Unravel
import Prelude hiding (lookup)
import Control.Monad (when)

-- Extract metrics from universe
getMetrics :: ExprV -> (Integer, Integer, Integer)
getMetrics expr = case run_thermo expr of
  Pair _ u -> (total_entropy u, time_step u, void_count u)

-- Test entropy bomb pattern (same as TypeScript)
entropyBomb :: Integer -> ExprV
entropyBomb 0 = EVDiv (EVNum 1) (EVNum 0)
entropyBomb n = EVAdd (entropyBomb (n-1)) (entropyBomb (n-1))

-- Test Noether's theorem
testNoether :: Integer -> Integer -> Bool
testNoether a b = 
  let entropy1 = case run_thermo (EVAdd (EVNum a) (EVNum b)) of Pair _ u -> total_entropy u
      entropy2 = case run_thermo (EVAdd (EVNum b) (EVNum a)) of Pair _ u -> total_entropy u
  in entropy1 == entropy2

main :: IO ()
main = do
  putStrLn "🔬 HASKELL REFERENCE COMPREHENSIVE STRESS TEST"
  putStrLn "Testing formal implementation to validate TypeScript behavior\n"
  
  -- Test 1: Entropy bomb progression
  putStrLn "=== ENTROPY BOMB TEST ==="
  putStrLn "Testing same pattern that caused TypeScript time anomalies...\n"
  
  mapM_ (\depth -> do
    let (entropy, time, voids) = getMetrics (entropyBomb depth)
    putStrLn $ "Bomb depth " ++ show depth ++ 
               ": entropy=" ++ show entropy ++ 
               ", time=" ++ show time ++ 
               ", voids=" ++ show voids
    ) [0..10]
  
  -- Test 2: Mathematical law stress
  putStrLn "\n=== MATHEMATICAL LAW STRESS TEST ==="
  putStrLn "Testing Noether's theorem across many cases...\n"
  
  let testRange = [1..100]
  let noetherResults = [testNoether a b | a <- testRange, b <- take 10 testRange]
  let violations = length (filter not noetherResults)
  let total = length noetherResults
  
  putStrLn $ "Noether tests: " ++ show violations ++ "/" ++ show total ++ " violations"
  putStrLn $ "Success rate: " ++ show (fromIntegral (total - violations) / fromIntegral total * 100) ++ "%"
  
  when (violations > 0) $
    putStrLn "🚨 MATHEMATICAL LAW VIOLATIONS IN HASKELL REFERENCE!"
  
  -- Test 3: Time evolution investigation
  putStrLn "\n=== TIME EVOLUTION INVESTIGATION ==="
  putStrLn "Comparing with TypeScript time anomaly patterns...\n"
  
  let timeTests = [
        ("Single void", EVDiv (EVNum 1) (EVNum 0)),
        ("Double void", EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVDiv (EVNum 2) (EVNum 0))),
        ("Variable cascade", EVLet "x" (EVDiv (EVNum 10) (EVNum 0)) 
                                    (EVAdd (EVVar "x") (EVVar "undefined"))),
        ("Complex combination", EVAdd (EVDiv (EVNum 100) (EVNum 0)) 
                                      (EVAdd (EVVar "missing") (EVMod (EVNum 50) (EVNum 0))))
        ]
  
  mapM_ (\(name, expr) -> do
    let (entropy, time, voids) = getMetrics expr
    putStrLn $ "  " ++ name ++ ": entropy=" ++ show entropy ++ 
               ", time=" ++ show time ++ ", voids=" ++ show voids
    
    -- Check for anomalies
    when (time < voids && voids > 1) $
      putStrLn $ "    🤔 TIME < VOIDS: Unusual pattern (time=" ++ show time ++ ", voids=" ++ show voids ++ ")"
    ) timeTests
  
  -- Test 4: High entropy scenarios
  putStrLn "\n=== HIGH ENTROPY SCENARIOS ==="
  putStrLn "Testing scenarios that pushed TypeScript to limits...\n"
  
  let highEntropyTest = foldl1 EVAdd [EVDiv (EVNum n) (EVNum 0) | n <- [1..15]]
  let (highEntropy, highTime, highVoids) = getMetrics highEntropyTest
  
  putStrLn $ "High entropy test: entropy=" ++ show highEntropy ++ 
             ", time=" ++ show highTime ++ ", voids=" ++ show highVoids
  
  when (highEntropy > 50) $
    putStrLn $ "  🔥 HIGH ENTROPY REACHED: " ++ show highEntropy
  
  when (highTime == highVoids) $
    putStrLn $ "  ✅ TIME MATCHES VOIDS: Consistent evolution"
  
  when (highTime /= highVoids) $
    putStrLn $ "  🤔 TIME DIVERGENCE: time=" ++ show highTime ++ " vs voids=" ++ show highVoids
  
  -- Test 5: Self-reference patterns
  putStrLn "\n=== SELF-REFERENCE PATTERNS ==="
  
  let selfRefTests = [
        ("Simple self-ref", EVLet "x" (EVVar "x") (EVVar "x")),
        ("Mutual reference", EVLet "a" (EVVar "b") (EVLet "b" (EVVar "a") (EVVar "a"))),
        ("Complex self-ref", EVLet "y" (EVAdd (EVVar "y") (EVNum 1)) (EVVar "y"))
        ]
  
  mapM_ (\(name, expr) -> do
    let result = run_basic expr
    let resultStr = case result of
          VNum n -> show n
          VVoid -> "VOID"  
          VBool b -> show b
    putStrLn $ "  " ++ name ++ ": " ++ resultStr
    ) selfRefTests
  
  putStrLn "\n🏆 HASKELL REFERENCE STRESS TEST COMPLETE"
  putStrLn "\n🎯 KEY FINDINGS:"
  putStrLn "Compare these results with TypeScript implementation to:"
  putStrLn "  1. Validate mathematical law compliance"  
  putStrLn "  2. Understand time evolution differences"
  putStrLn "  3. Identify implementation-specific behaviors"
  putStrLn "  4. Confirm production readiness assessment"
  
  putStrLn "\n🌀 Formal reference implementation tested! 🌀"