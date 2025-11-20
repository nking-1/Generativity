module Main where

import UnravelMonad
import ThermoLang
import qualified Prelude
import Prelude hiding (div, (/))

-- ==========================================
-- 1. THE PHYSICS OF REFACTORING
-- ==========================================

-- The "Current" is the vector of conserved quantities
data NoetherCurrent = Current {
    sFlux :: Int, -- Entropy Flux (S)
    tFlux :: Int  -- Time Flux (T)
} deriving (Eq, Show)

-- Measure the current of a program
measure :: Term -> NoetherCurrent
measure term = 
    let stats = analyze term -- Using the static analyzer from ThermoLang
    in Current (maxEntropy stats) (timeCost stats)

-- ==========================================
-- 2. THE SYMMETRY CHECKER
-- ==========================================

data RefactorStatus 
    = ExactSymmetry      -- Perfect Refactor (S=, T=)
    | Optimization       -- Better Physics (S<=, T<)
    | TradeOff           -- Different Physics (S decreases, T increases or vice versa)
    | Regression         -- Worse Physics (S>)
    deriving (Show)

checkSymmetry :: Term -> Term -> IO ()
checkSymmetry old new = do
    let c1 = measure old
    let c2 = measure new
    
    let deltaS = sFlux c2 Prelude.- sFlux c1
    let deltaT = tFlux c2 Prelude.- tFlux c1
    
    putStrLn $ "  Old Current: S=" ++ show (sFlux c1) ++ " T=" ++ show (tFlux c1)
    putStrLn $ "  New Current: S=" ++ show (sFlux c2) ++ " T=" ++ show (tFlux c2)
    putStrLn $ "  Delta:       ΔS=" ++ show deltaS ++ " ΔT=" ++ show deltaT
    
    case (compare deltaS 0, compare deltaT 0) of
        (EQ, EQ) -> putStrLn "  => ✅ EXACT SYMMETRY (Safe Refactor)"
        (EQ, LT) -> putStrLn "  => ✨ PURE OPTIMIZATION (Faster, same Safety)"
        (LT, _)  -> putStrLn "  => 🛡️  ENTROPY REDUCTION (Code became safer)"
        (GT, _)  -> putStrLn "  => 🚨 NOETHER VIOLATION (Entropy Leak / Regression)"
        (_, GT)  -> putStrLn "  => 🐌 DEGRADATION (Code became slower)"
        
-- ==========================================
-- 3. DEMONSTRATION SCENARIOS
-- ==========================================

-- Scenario A: Commutativity (Refactoring a + b to b + a)
oldA = Add (Val 10) (Div (Val 1) (Val 0))
newA = Add (Div (Val 1) (Val 0)) (Val 10)

-- Scenario B: Constant Folding (Optimization)
oldB = Add (Val 10) (Val 20)
newB = Val 30

-- Scenario C: Introducing a Bug (Regression)
oldC = Div (Val 10) (Val 10) -- Safe-ish (Static analyzer assumes worst case for Div though)
newC = Div (Val 10) (Val 0)  -- Analyzer sees Div as Div, but let's try nested

-- Let's verify Loop Unrolling (Should be Symmetry or Optimization?)
-- Loop 2 (Add 1 1)
oldLoop = Repeat 2 (Add (Val 1) (Val 1))
-- Add 1 1 + Add 1 1
newLoop = Add (Add (Val 1) (Val 1)) (Add (Val 1) (Val 1))

-- Dead Code Elimination
-- If (Void) then (1) else (2) -> Analyzer sums both (Conservative)
-- If we remove the void branch, S drops.
oldDead = Shield (Div (Val 1) (Val 0)) (Val 10)
newDead = Val 10 -- Manual optimization

-- Replacing Safe Math with Risky Math
oldSafe = Add (Val 10) (Val 10)  -- Entropy 0
newRisky = Div (Val 100) (Val 1) -- Entropy 1 (Analyzer assumes worst case for Div)


main :: IO ()
main = do
    putStrLn "=== NOETHER COMPILER LINTER ==="
    putStrLn "Checking Code Changes for Thermodynamic Conservation\n"
    
    putStrLn "--- Test 1: Commutative Refactor (a+b -> b+a) ---"
    checkSymmetry oldA newA
    
    putStrLn "\n--- Test 2: Constant Folding (10+20 -> 30) ---"
    checkSymmetry oldB newB
    
    putStrLn "\n--- Test 3: Loop Unrolling (Repeat 2 -> Inline) ---"
    -- Note: Repeat multiplies costs. Add sums costs.
    -- Repeat 2 (Cost 1) = Cost 2
    -- Add (Cost 1) (Cost 1) + Base(1) = Cost 3
    -- Unrolling actually ADDS structural overhead (the Add node)!
    checkSymmetry oldLoop newLoop
    
    putStrLn "\n--- Test 4: Removing Safety Shield (Regression?) ---"
    -- Removing the shield around a risky op
    let safe = Shield (Div (Val 1) (Val 0)) (Val 0)
    let risky = Div (Val 1) (Val 0)
    checkSymmetry safe risky

    putStrLn "\n--- Test 5: Dead Code Elimination (Optimization) ---"
    checkSymmetry oldDead newDead

    putStrLn "\n--- Test 6: Safe vs Risky Math (Bug / regression) ---"
    checkSymmetry oldSafe newRisky
    
    putStrLn "\n=== ANALYSIS COMPLETE ==="