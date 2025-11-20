module Main where

import UnravelMonad
import ThermoLang
import qualified Prelude
import Prelude hiding (div, (/))

-- ==========================================
-- DEMO PROGRAMS
-- ==========================================

-- Program 1: Pure Math (Safe)
-- 10 + 20
progSafe :: Term
progSafe = Add (Val 10) (Val 20)

-- Program 2: The Risk (Single Division)
-- 100 / x (where x might be 0)
progRisky :: Term
progRisky = Div (Val 100) (Val 0)

-- Program 3: The Loop (Entropy Multiplication)
-- Repeat 10 times: (1 / 0)
-- This demonstrates "Loop Entropy"
progLoop :: Term
progLoop = Repeat 10 (Div (Val 1) (Val 0))

-- Program 4: The Shield (Recovery)
-- Try (1/0), but catch it. 
-- Compiler knows entropy still exists!
progShield :: Term
progShield = Shield (Div (Val 1) (Val 0)) (Val 999)

-- Program 5: The Infinite Loop (Rejected)
-- Repeat 10,001 times
progTooHeavy :: Term
progTooHeavy = Repeat 10001 (Add (Val 1) (Val 1))

-- ==========================================
-- COMPILER RUNNER
-- ==========================================

runTest :: String -> Term -> IO ()
runTest name term = do
    putStrLn $ "\n--- Compiling: " ++ name ++ " ---"
    case build term of
        Rejected reason -> do
            putStrLn $ "❌ COMPILATION FAILED: " ++ reason
            
        Accepted stats executable -> do
            putStrLn $ "✅ COMPILATION SUCCESS"
            putStrLn $ "   Predicted Entropy: " ++ show (maxEntropy stats)
            putStrLn $ "   Predicted Cost:    " ++ show (timeCost stats)
            putStrLn $ "   Is Pure?           " ++ show (isSafe stats)
            
            putStrLn "   Executing..."
            let (res, u) = run executable
            
            putStrLn $ "   Actual Result:  " ++ show res
            putStrLn $ "   Actual Entropy: " ++ show (totalEntropy u)
            
            -- Verify prediction
            if totalEntropy u Prelude.<= maxEntropy stats
                then putStrLn "   ✓ Theory holds (Actual <= Predicted)"
                else putStrLn "   🚨 ANOMALY: Entropy exceeded prediction!"

main :: IO ()
main = do
    putStrLn "=== THERMOLANG COMPILER v1.0 ==="
    putStrLn "Demonstrating Totality & Entropy Bounds at Compile Time"
    
    runTest "Safe Math" progSafe
    runTest "Risky Division" progRisky
    runTest "Entropy Loop" progLoop
    runTest "Shielded Logic" progShield
    runTest "Massive Loop" progTooHeavy
    
    putStrLn "\n=== DEMO COMPLETE ==="