module Main where

import UnravelMonad
import ThermoLangV2
import qualified Prelude
import Prelude hiding (div, (/))

-- ============================================================================
-- 😈 THE DIABOLICAL SUITE
-- ============================================================================

-- TEST 1: THE HYDRA (Fractal Failure)
-- Nested Maps. If the outer value causes the inner map to fail, 
-- does the entropy multiply correctly?
-- Logic: 
--   outer = [1, 0, 2]
--   inner = [10, 20, 30]
--   map x in outer:
--     map y in inner:
--       y / x
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

-- TEST 2: THE TYPE-CHECKER BLIND SPOT (Noether Violation)
-- Our Static Analyzer checks *Arithmetic* entropy (Div).
-- It does NOT check *Type* entropy (LogicError).
-- This test deliberately provokes a type error to show that 
-- Runtime Entropy > Predicted Entropy (The model is incomplete).
typeChaos :: Term
typeChaos = Add (IntVal 10) (BoolVal True) 

-- TEST 3: THE SCHRODINGER CONDITIONAL
-- What happens if the *condition* of an IF is Void?
-- Standard Logic: Crash.
-- Thermo Logic: The Void propagates. The branches are irrelevant.
schrodingerIf :: Term
schrodingerIf = 
    If (Eq (Div (IntVal 1) (IntVal 0)) (IntVal 0)) -- Condition is Void
       (IntVal 100) -- True branch
       (IntVal 200) -- False branch

-- TEST 4: THE BLACK HOLE AGGREGATOR
-- A Fold that consumes itself.
-- Logic: Fold (+) 0 [10, 5, 0, 2]
-- But inside the fold: acc + (100 / val)
-- When val is 0, that step is Void. 
-- Does Fold absorb the void and continue with the old accumulator?
-- Or does the whole Fold collapse?
-- (Note: Our Fold implementation in ThermoLangV2 uses foldM. 
--  If a step returns Void, foldM in Unravel Monad propagates Void.
--  So the *entire* result should be Void, but entropy should be sum of steps + 1)
blackHoleFold :: Term
blackHoleFold = 
    Let "data" (ListVal [IntVal 10, IntVal 0, IntVal 5])
    (Fold "acc" "x"
        (Add (Var "acc") (Div (IntVal 100) (Var "x")))
        (IntVal 0)
        (Var "data")
    )

-- ==========================================
-- RUNNER
-- ==========================================

runTest :: String -> Term -> IO ()
runTest name term = do
    putStrLn $ "\n🔥 TEST: " ++ name
    
    case build term of
        Rejected reason -> putStrLn $ "❌ Rejected: " ++ reason
        Accepted stats executable -> do
            putStrLn $ "   Predicted Entropy: " ++ show (maxEntropy stats)
            
            let (res, u) = run executable
            
            putStrLn $ "   Actual Entropy:    " ++ show (totalEntropy u)
            putStrLn $ "   Void Count:        " ++ show (voidCount u)
            putStrLn $ "   Result:            " ++ case res of
                Valid v   -> show v
                Invalid i -> "Void (" ++ show (source i) ++ ")"

            -- Verification Logic
            if totalEntropy u Prelude.> maxEntropy stats
                then putStrLn "   ⚠️  ANOMALY: Actual > Predicted (Model Underestimation)"
                else putStrLn "   ✓  Model Safe (Actual <= Predicted)"

main :: IO ()
main = do
    putStrLn "=== 😈 DIABOLICAL STRESS TEST (ThermoLang V2) ==="
    
    runTest "The Hydra (Nested Maps)" hydra
    -- Expectation: 
    -- Outer loop runs 3 times.
    -- Inner loop runs 3 times per outer (Total 9 ops).
    -- When x=0 (1 case), inner loop runs 3 times.
    -- 3 divisions by zero occur.
    -- Harvest absorbs them?
    -- Let's see.
    
    runTest "Type Chaos (The Blind Spot)" typeChaos
    -- Expectation:
    -- Analyzer sees Add(Val, Val). Predicts Entropy 0.
    -- Runtime sees Int + Bool. Fails. Entropy 1.
    -- This proves we need a Type Checker for total accuracy.
    
    runTest "Schrodinger's If" schrodingerIf
    -- Expectation:
    -- Condition is Void. Entropy 1.
    -- Result should be Void.
    
    runTest "Black Hole Fold" blackHoleFold
    -- Expectation:
    -- Fold is sequential (monadic).
    -- Step 1 (10): OK.
    -- Step 2 (0): Void.
    -- Step 3 (5): Skipped? Or does foldM propagate?
    -- In Unravel Monad (>>=), failure short circuits.
    -- So result is Void.
    
    putStrLn "\n=== SUITE COMPLETE ==="