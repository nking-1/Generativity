module Main where

import UnravelMonad
import Control.Monad (when, forM_)
import Text.Printf (printf)

-- ==========================================
-- HELPERS
-- ==========================================

-- Extract metrics for assertions
getMetrics :: Unravel a -> (Int, Int)
getMetrics prog = 
    let (_, u) = run prog
    in (totalEntropy u, timeStep u)

-- Pretty print result
printThermo :: Show a => Unravel a -> IO ()
printThermo prog = do
    let (res, u) = run prog
    putStrLn $ case res of
        Valid v   -> "  Value: " ++ show v
        Invalid _ -> "  Value: Void"
    putStrLn $ "  Entropy: " ++ show (totalEntropy u)
    putStrLn $ "  Time:    " ++ show (timeStep u)
    putStrLn $ "  Voids:   " ++ show (voidCount u)

-- ==========================================
-- 1. THE ENTROPY BOMB (Clean Syntax)
-- ==========================================

-- Look how clean this is compared to the raw version!
-- It looks like pure math, but runs thermodynamics.
entropyBomb :: Int -> Unravel Int
entropyBomb 0 = uDiv 1 0
entropyBomb n = 
    let prev = entropyBomb (n - 1)
    in prev |+| prev -- Using applicative add to combine voids

testEntropyBomb :: IO ()
testEntropyBomb = do
    putStrLn "\n=== 💥 TEST 1: THE ENTROPY BOMB (Clean Syntax) ==="
    putStrLn "Verifying exponential entropy growth..."
    
    forM_ [0..10] $ \n -> do
        let (e, t) = getMetrics (entropyBomb n)
        putStrLn $ printf "Depth %2d: Entropy=%-6d Time=%-6d Ratio=%.2f" n e t (fromIntegral e / fromIntegral t :: Double)
        
    let (e10, _) = getMetrics (entropyBomb 10)
    if e10 > 10000 
        then putStrLn "✅ SUCCESS: Entropy explosion confirmed."
        else putStrLn "❌ FAILURE: Entropy did not grow exponentially."

-- ==========================================
-- 2. NOETHER'S THEOREM (Symmetry)
-- ==========================================

testNoether :: IO ()
testNoether = do
    putStrLn "\n=== ⚖️  TEST 2: NOETHER'S THEOREM ==="
    putStrLn "Verifying that symmetry preserves conservation..."
    
    let a = uDiv 10 0 -- Void(1)
    let b = return 5  -- Valid(5)
    
    let (e1, _) = getMetrics (a |+| b)
    let (e2, _) = getMetrics (b |+| a)
    
    putStrLn $ "Entropy (Void + 5): " ++ show e1
    putStrLn $ "Entropy (5 + Void): " ++ show e2
    
    if e1 == e2
        then putStrLn "✅ SUCCESS: Commutative symmetry holds for Void."
        else putStrLn "❌ FAILURE: Symmetry violation."

-- ==========================================
-- 3. RECOVERY CONSERVATION
-- ==========================================

testRecovery :: IO ()
testRecovery = do
    putStrLn "\n=== 🛡️  TEST 3: CONSERVATION OF RECOVERY ==="
    putStrLn "Verifying that healing a void does not erase history..."
    
    let badCalc = uDiv 1 0 |+| uDiv 2 0 -- Should have entropy ~3
    let healed  = recover badCalc 42
    
    let (res, u) = run healed
    
    putStrLn $ "Result Value: " ++ show res
    putStrLn $ "System Entropy: " ++ show (totalEntropy u)
    
    case res of
        Valid 42 -> 
            if totalEntropy u > 0 
                then putStrLn "✅ SUCCESS: Value recovered but Entropy persisted."
                else putStrLn "❌ FAILURE: Entropy was erased."
        _ -> putStrLn "❌ FAILURE: Value was not recovered."

-- ==========================================
-- 4. THE "WHEEL" ARITHMETIC
-- ==========================================

testWheel :: IO ()
testWheel = do
    putStrLn "\n=== 🎡 TEST 4: WHEEL ARITHMETIC ==="
    putStrLn "Verifying Nullity/Infinity absorption..."
    
    let inf = uDiv 1 0
    let calc = (inf |+| return 100) |*| return 2
    
    let (res, u) = run calc
    
    case res of
        Invalid _ -> putStrLn "✅ SUCCESS: Infinity absorbed operations."
        Valid v   -> putStrLn $ "❌ FAILURE: Infinity leaked value: " ++ show v

-- ==========================================
-- MAIN RUNNER
-- ==========================================

main :: IO ()
main = do
    putStrLn "Running Unravel Monad Test Suite..."
    testEntropyBomb
    testNoether
    testRecovery
    testWheel
    putStrLn "\nAll tests executed."