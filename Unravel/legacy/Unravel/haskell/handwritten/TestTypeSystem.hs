module Main where

import ThermoTypeSystem
import ThermoLangV2
import qualified Prelude
import Prelude hiding (div, (/))

-- Re-importing the problematic term from Diabolical suite
typeChaos :: Term
typeChaos = Add (IntVal 10) (BoolVal True)

-- A valid term for comparison
typeSafe :: Term
typeSafe = Add (IntVal 10) (IntVal 20)

-- The "Hydra" (Nested Map) - Should pass typing!
hydra :: Term
hydra = 
    Let "outer" (ListVal [IntVal 1, IntVal 0, IntVal 2])
    (Let "inner" (ListVal [IntVal 10, IntVal 20, IntVal 30])
        (Map "x"
            (Map "y" 
                (Div (Var "y") (Var "x"))
                (Var "inner")
            )
            (Var "outer")
        )
    )

-- Broken Map (Mapping math over booleans)
brokenMap :: Term
brokenMap = 
    Let "list" (ListVal [BoolVal True, BoolVal False])
        (Map "x" (Add (Var "x") (IntVal 1)) (Var "list"))

runCheck :: String -> Term -> IO ()
runCheck name term = do
    putStrLn $ "--- Checking: " ++ name ++ " ---"
    case analyzeTyped term of
        Left err -> do
            putStrLn $ "🛑 TYPE ERROR: " ++ show err
            putStrLn "   (Entropy calculation aborted - Program Rejected)"
        Right stats -> do
            putStrLn "✅ TYPE CHECK PASSED"
            putStrLn $ "   Thermodynamics: " ++ show stats

main :: IO ()
main = do
    putStrLn "=== THERMODYNAMIC TYPE SYSTEM ==="
    putStrLn "Verifying that Logic Errors are caught before Thermodynamics...\n"

    runCheck "Safe Math" typeSafe
    runCheck "Type Chaos (Int + Bool)" typeChaos
    runCheck "The Hydra (Complex but Valid)" hydra
    runCheck "Broken Map (Math on Bools)" brokenMap

    putStrLn "\n=== SUITE COMPLETE ==="