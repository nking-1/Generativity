-- SimpleV2Test.hs  
-- Simple stress test of UnravelCleanV2 to compare with TypeScript

import UnravelCleanV2
import Control.Monad (when)

-- Entropy bomb for V2
entropyBombV2 :: Integer -> ExprV
entropyBombV2 0 = EVDiv (EVNum 1) (EVNum 0)
entropyBombV2 n = EVAdd (entropyBombV2 (n-1)) (entropyBombV2 (n-1))

-- Extract universe metrics
getV2Metrics :: ExprV -> (Integer, Integer, Integer)
getV2Metrics expr = case runThermo expr of
  (v, u) -> (totalEntropy u, timeStep u, voidCount u)

main :: IO ()
main = do
  putStrLn "🔬 UNRAVEL V2 SIMPLE STRESS TEST"
  putStrLn "Testing V2 clean reference vs TypeScript implementation\n"
  
  -- Test 1: Entropy bomb (the key diagnostic)
  putStrLn "=== V2 ENTROPY BOMB TEST ==="
  putStrLn "Same pattern that revealed TypeScript issues...\n"
  
  mapM_ (\depth -> do
    let (entropy, time, voids) = getV2Metrics (entropyBombV2 depth)
    putStrLn $ "V2 Bomb " ++ show depth ++ 
               ": entropy=" ++ show entropy ++ 
               ", time=" ++ show time ++ 
               ", voids=" ++ show voids
    
    -- Flag any unusual patterns
    when (time /= voids && depth > 0) $
      putStrLn $ "  🤔 TIME/VOID DIVERGENCE: " ++ show time ++ " vs " ++ show voids
    
    when (depth > 5 && entropy > 100) $
      putStrLn $ "  🔥 HIGH ENTROPY: " ++ show entropy
    ) [0..10]
  
  -- Test 2: Mathematical laws
  putStrLn "\n=== V2 MATHEMATICAL LAWS ==="
  
  let testCases = [
        (EVAdd (EVNum 42) (EVNum 58), EVAdd (EVNum 58) (EVNum 42), "Commutativity"),
        (EVAdd (EVAdd (EVNum 1) (EVNum 2)) (EVNum 3), EVAdd (EVNum 1) (EVAdd (EVNum 2) (EVNum 3)), "Associativity"),
        (EVDiv (EVNum 10) (EVNum 0), EVDiv (EVNum 20) (EVNum 0), "Void equivalence")
        ]
  
  mapM_ (\(expr1, expr2, name) -> do
    let (e1, t1, v1) = getV2Metrics expr1
    let (e2, t2, v2) = getV2Metrics expr2
    let equivalent = e1 == e2
    
    putStrLn $ "  " ++ name ++ ": " ++ show e1 ++ " vs " ++ show e2 ++ 
               " → " ++ (if equivalent then "✓" else "✗")
    ) testCases
  
  -- Test 3: Variable environment
  putStrLn "\n=== V2 VARIABLE TESTS ==="
  
  let varTests = [
        ("Self-ref", EVLet "x" (EVVar "x") (EVVar "x")),
        ("Undefined", EVVar "nonexistent"),
        ("Normal let", simpleLet),
        ("Complex vars", complexWithVars)
        ]
  
  mapM_ (\(name, expr) -> do
    let (v, u) = runThermo expr
    let resultStr = case v of
          VTNum n -> show n
          VTVoid _ -> "VOID"
          VTBool b -> show b
    putStrLn $ "  " ++ name ++ ": " ++ resultStr ++ 
               " (entropy=" ++ show (totalEntropy u) ++ ")"
    ) varTests
  
  putStrLn "\n🎯 V2 ANALYSIS COMPLETE"
  putStrLn "Compare these results with TypeScript to identify improvements needed!"