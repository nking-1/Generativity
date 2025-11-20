module Main where

import ThermoParser
import ThermoTypeSystem
import ThermoLangV2
import UnravelMonad
import qualified Prelude
import Prelude hiding (div, (/))

-- ==========================================
-- DEMO SCRIPTS (The "Real" Language)
-- ==========================================

script1_pipeline :: String
script1_pipeline = unlines
  [ "let data = [10, 5, 0, 20] in"
  , "let processed = map(x -> 100 / x, data) in"
  , "fold(acc, val -> acc + val, 0, processed)"
  ]

script2_shield :: String
script2_shield = 
  "shield (10 / 0) recover 999"

script3_logic :: String
script3_logic = 
  "if (10 + 5) == 15 then 100 else 0"

script4_nested :: String
script4_nested = unlines
  [ "let x = 10 in"
  , "let y = 0 in"
  , "if x == 0 then 0 else (x / y)" -- Should be Void
  ]

script5_syntax_error :: String
script5_syntax_error = 
  "let x = 10 in map( -> , data)" -- Missing var

-- ==========================================
-- RUNNER
-- ==========================================

runScript :: String -> String -> IO ()
runScript name code = do
    putStrLn $ "\n📜 SCRIPT: " ++ name
    putStrLn $ "   Code: " ++ code
    
    -- 1. PARSE
    case parseThermo code of
        Left err -> putStrLn $ "❌ PARSE ERROR:\n" ++ err
        
        Right ast -> do
            putStrLn "   ✅ Parsed AST."
            
            -- 2. COMPILE & ANALYZE (Type + Thermo)
            case analyzeTyped ast of
                Left typeErr -> putStrLn $ "🛑 TYPE ERROR: " ++ show typeErr
                
                Right stats -> do
                    putStrLn $ "   ✅ Type Check Passed."
                    putStrLn $ "   Predicted Entropy: " ++ show (maxEntropy stats)
                    putStrLn $ "   Predicted Cost:    " ++ show (timeCost stats)
                    
                    -- 3. EXECUTE
                    putStrLn "   Executing..."
                    let (res, u) = run (compile ast Prelude.mempty)
                    
                    putStrLn $ "   Result:  " ++ show res
                    putStrLn $ "   Entropy: " ++ show (totalEntropy u)
                    putStrLn $ "   Time:    " ++ show (timeStep u)

main :: IO ()
main = do
    putStrLn "=== THERMOLANG FULL STACK DEMO ==="
    putStrLn "String -> Parser -> TypeCheck -> Analyzer -> Runtime"
    
    runScript "The Resilient Pipeline" script1_pipeline
    runScript "Shield Syntax" script2_shield
    runScript "Logic Test" script3_logic
    runScript "Runtime Failure" script4_nested
    runScript "Syntax Error Test" script5_syntax_error
    
    putStrLn "\n=== DEMO COMPLETE ==="