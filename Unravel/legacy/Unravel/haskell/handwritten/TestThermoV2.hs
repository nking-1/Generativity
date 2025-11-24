module Main where

import UnravelMonad
import ThermoLangV2
import qualified Prelude
import Prelude hiding (div, (/))

-- ==========================================
-- THE "BUSINESS LOGIC" (Data Analysis)
-- ==========================================

-- Scenario: 
-- We receive a list of Transactions. 
-- Each transaction is [Amount, Rate].
-- We want to calculate: sum(Amount / Rate) for valid transactions.
-- Rates can be 0 (Error).

-- Logic:
-- let results = map (\t -> t[0] / t[1]) transactions
-- fold (\acc x -> acc + x) 0 results

-- REVISED LOGIC: 
-- We'll just use a list of Integers and map (100 / x).
-- Much simpler for demo.
apiGatewayDemo :: Term
apiGatewayDemo = 
    Let "inputs" (ListVal [IntVal 10, IntVal 5, IntVal 0, IntVal 2, IntVal 0])
        (Let "normalized" 
            (Map "x" (Div (IntVal 100) (Var "x")) (Var "inputs"))
            (Fold "acc" "val" (Add (Var "acc") (Var "val")) (IntVal 0) (Var "normalized"))
        )

-- ==========================================
-- EXECUTION
-- ==========================================

main :: IO ()
main = do
    putStrLn "=== 🌐 THERMODYNAMIC API GATEWAY ==="
    putStrLn "Request: Batch Process 5 items (2 Malformed)"
    
    case build apiGatewayDemo of
        Rejected reason -> putStrLn $ "❌ Compiler Rejected: " ++ reason
        Accepted stats executable -> do
            putStrLn "✅ Compiled Successfully."
            putStrLn $ "   Predicted Max Entropy: " ++ show (maxEntropy stats)
            putStrLn $ "   Predicted Cost:        " ++ show (timeCost stats)
            
            putStrLn "\n--- EXECUTING REQUEST ---"
            let (res, u) = run executable
            
            putStrLn $ "   System Entropy: " ++ show (totalEntropy u)
            putStrLn $ "   System Time:    " ++ show (timeStep u)
            putStrLn $ "   Void Count:     " ++ show (voidCount u)
            
            case res of
                Valid (VInt val) -> do
                    putStrLn $ "\n✅ RESPONSE: 200 OK"
                    putStrLn $ "   Payload: " ++ show val
                    putStrLn "   (Note: Result includes only valid items: 10+20+50 = 80)"
                    
                    if totalEntropy u == 2 
                        then putStrLn "   ✓ Thermodynamics verified: 2 Voids absorbed."
                        else putStrLn "   ❓ Entropy anomaly."
                        
                Valid v -> putStrLn $ "⚠️ Unexpected return type: " ++ show v
                Invalid _ -> putStrLn "❌ RESPONSE: 500 Internal Server Error (Logic Collapse)"