module Main where

import UnravelMonad
import Control.Monad (forM_)
import Text.Printf (printf)

-- ==========================================
-- THE SCENARIO
-- ==========================================

type SensorData = (Int, Int) -- (Value, Calibration)

rawData :: [SensorData]
rawData = [ (100, 10)  -- Valid: 10
          , (50, 5)    -- Valid: 10
          , (200, 0)   -- BAD: Div by zero
          , (300, 30)  -- Valid: 10
          , (500, 0)   -- BAD: Div by zero
          , (40, 4)    -- Valid: 10
          ]

processSensor :: SensorData -> Unravel Int
processSensor (val, cal) = uDiv val cal

-- The Pipeline
pipeline :: Unravel Int
pipeline = do
    let operations = map processSensor rawData
    
    -- Use the LIBRARY version of harvest (linear time)
    cleanData <- harvest operations
    
    let total = sum cleanData
    let count = length cleanData
    
    uDiv total count

-- ==========================================
-- TEST RUNNER
-- ==========================================

main :: IO ()
main = do
    putStrLn "=== 🏭 TEST: RESILIENT DATA PIPELINE ==="
    putStrLn "Processing sensor data with corrupted entries..."
    putStrLn $ "Input Data: " ++ show rawData
    
    let (res, u) = run pipeline
    
    putStrLn "\n--- RESULTS ---"
    case res of
        Valid avg -> putStrLn $ "✅ Pipeline Succeeded! Average: " ++ show avg
        Invalid _ -> putStrLn "❌ Pipeline Failed (Should not happen with harvest)"
        
    putStrLn "\n--- THERMODYNAMICS ---"
    putStrLn $ "Total System Entropy: " ++ show (totalEntropy u)
    putStrLn $ "Total Void Count:     " ++ show (voidCount u)
    putStrLn $ "Time Steps:           " ++ show (timeStep u)
    
    putStrLn "\n--- ANALYSIS ---"
    if totalEntropy u == 2 
        then putStrLn "✅ ENTROPY CHECK: Exactly 2 voids were absorbed (Correct)."
        else putStrLn $ "❌ ENTROPY CHECK: Expected 2, got " ++ show (totalEntropy u)
        
    if timeStep u > 0
        then putStrLn "✅ TIME CHECK: Time is flowing."
        else putStrLn "❌ TIME CHECK: Time stopped."