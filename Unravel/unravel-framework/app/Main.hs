module Main where

import Control.Monad.Unravel
import Control.Monad.Unravel.SafeIO
import Data.Unravel.Universe
import Control.Monad (foldM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.Char (chr)

-- ==========================================
-- 1. DOMAIN LOGIC (The Reactor)
-- ==========================================

data ReactorState = ReactorState {
    temp      :: Int,
    power     :: Int,
    isScrammed :: Bool
} deriving (Show)

initialState :: ReactorState
initialState = ReactorState 300 0 False

-- Simulated Sensor Data
-- Some files exist, some don't (IO Errors).
-- Some values are valid, some are 0 (Math Errors).
sensorFiles :: [String]
sensorFiles = ["sensor_core.txt", "sensor_coolant.txt", "sensor_turbine.txt"]

-- The Control Loop Logic
-- This function has NO error handling logic inside it. 
-- It assumes happy paths. The Framework handles the chaos.
controlLoop :: ReactorState -> String -> UnravelT IO ReactorState
controlLoop state sensorFile = do
    -- 1. Work cost (Overhead of reading sensors)
    work 5
    
    -- 2. Try to read the sensor (IO Risk)
    content <- safeIO $ readFile sensorFile
    let val = read content :: Int
    
    safeIO $ putStrLn $ "   [SENSOR] Read " ++ sensorFile ++ ": " ++ show val
    
    -- 3. Calculate Efficiency (Math Risk)
    -- Efficiency = Power / SensorValue. If Sensor is 0, Singularity.
    efficiency <- safeDiv 1000 val
    
    -- 4. Update State (Business Logic)
    work 10 -- Heavy calculation cost
    let newTemp = temp state + 10
    let newPower = power state + efficiency
    
    return $ state { temp = newTemp, power = newPower }

-- ==========================================
-- 2. THE RESILIENT PIPELINE
-- ==========================================

runSimulation :: UnravelT IO ReactorState
runSimulation = do
    -- Setup the environment (Create some files, delete others to simulate failure)
    -- Note: We use liftIO here for setup, not safeIO, because we WANT this to crash if setup fails.
    liftIO $ writeFile "sensor_core.txt" "50"    -- Valid
    liftIO $ writeFile "sensor_turbine.txt" "0"  -- Singularity (DivByZero)
    -- "sensor_coolant.txt" is MISSING (IO Error)

    safeIO $ putStrLn "⚡ REACTOR STARTUP SEQUENCE INITIATED..."

    -- Define the step logic separately to avoid indentation errors
    let simulationStep currentState file = do
            -- THE SHIELD:
            -- We wrap the control loop. If it explodes (IO or Math), we catch it,
            -- record the entropy, and return the previous state (no change).
            shield (controlLoop currentState file) currentState

    -- Run the control loop using foldM
    finalState <- foldM simulationStep initialState sensorFiles

    return finalState

-- ==========================================
-- 3. HOLOGRAPHIC DECODER (Simple Version)
-- ==========================================

-- A simple decoder to verify the hologram contents for the demo
decodeHologram :: Integer -> [String]
decodeHologram 0 = []
decodeHologram n = 
    let (rest, digit) = n `divMod` 256
        -- 1 = DivZero, 2 = IO Error, 3 = Logic Error
        event = case digit of
            1 -> "💥 Singularity (DivByZero) "
            2 -> "🔌 Hardware Failure (IO Error) "
            3 -> "🐛 Logic Corruption "
            30 -> " [" -- Msg Start
            31 -> "] " -- Msg End
            c  -> [chr (fromIntegral c)] -- ASCII
    in decodeHologram rest ++ [event] 

-- ==========================================
-- 4. MAIN RUNNER
-- ==========================================

main :: IO ()
main = do
    (res, u) <- runUnravelT runSimulation
    
    putStrLn "\n============================================"
    putStrLn "       ⚛️  UNRAVEL REACTOR CORE  ⚛️"
    putStrLn "============================================"
    
    case res of
        Valid state -> putStrLn $ "\n✅ SYSTEM STATUS: ONLINE\n" ++ show state
        Invalid _   -> putStrLn "\n❌ SYSTEM STATUS: CRITICAL FAILURE"

    putStrLn "\n📊 THERMODYNAMIC TELEMETRY"
    putStrLn "--------------------------"
    putStrLn $ "Mass (Work Done):   " ++ show (mass u) ++ " units"
    putStrLn $ "Entropy (S):        " ++ show (structEntropy u + timeEntropy u) ++ " bits"
    putStrLn $ "Time Steps (t):     " ++ show (timeStep u) ++ " ticks"
    
    let s = fromIntegral (structEntropy u + timeEntropy u) :: Double
    let m = fromIntegral (mass u) :: Double
    let density = if m > 0 then s / m else 0
    
    putStrLn $ "Defect Density (ρ): " ++ take 5 (show density) 

    putStrLn "\n📼 HOLOGRAPHIC BLACK BOX RECORD"
    putStrLn "-------------------------------"
    putStrLn $ "Signature: " ++ show (boundaryValue u)
    putStrLn "\nDecoded Events:"
    
    -- Clean up the decoding output for display
    let rawEvents = decodeHologram (boundaryValue u)
    mapM_ putStr rawEvents
    putStrLn ""
    
    putStrLn "\n============================================"
    
    -- Clean up
    _ <- tryIO "sensor_core.txt"
    _ <- tryIO "sensor_turbine.txt"
    return ()
  where
    tryIO f = Prelude.writeFile f "" -- Dummy cleanup