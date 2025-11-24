module Main where

import Control.Monad.Unravel
import Control.Monad.Unravel.SafeIO
import Data.Unravel.Universe
import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)

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

sensorFiles :: [String]
sensorFiles = ["sensor_core.txt", "sensor_coolant.txt", "sensor_turbine.txt"]

controlLoop :: ReactorState -> String -> UnravelT IO ReactorState
controlLoop state sensorFile = do
    work 5
    content <- safeIO $ readFile sensorFile
    let val = read content :: Int
    safeIO $ putStrLn $ "   [SENSOR] Read " ++ sensorFile ++ ": " ++ show val
    efficiency <- safeDiv 1000 val
    work 10 
    let newTemp = temp state + 10
    let newPower = power state + efficiency
    return $ state { temp = newTemp, power = newPower }

-- ==========================================
-- 2. THE RESILIENT PIPELINE
-- ==========================================

runSimulation :: UnravelT IO ReactorState
runSimulation = do
    liftIO $ writeFile "sensor_core.txt" "50"    
    liftIO $ writeFile "sensor_turbine.txt" "0"  
    
    safeIO $ putStrLn "⚡ REACTOR STARTUP SEQUENCE INITIATED..."

    let simulationStep currentState file = do
            shield (controlLoop currentState file) currentState

    finalState <- foldM simulationStep initialState sensorFiles
    return finalState

-- ==========================================
-- 3. HELPER: PRETTY PRINTER
-- ==========================================

printPath :: String -> ParadoxPath -> IO ()
printPath indent p = case p of
    BaseVeil src -> putStrLn $ indent ++ "💥 " ++ show src
    SelfContradict next -> do
        putStrLn $ indent ++ "⏳ Time Step (Next) ->"
        printPath (indent ++ "  ") next
    Compose p1 p2 -> do
        putStrLn $ indent ++ "🔀 Entangled Branch {"
        printPath (indent ++ "  L: ") p1
        printPath (indent ++ "  R: ") p2
        putStrLn $ indent ++ "}"

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
    
    -- USE THE LIBRARY RECONSTRUCTOR!
    let history = reconstruct (boundaryValue u)
    
    if null history 
        then putStrLn "   (Clean Flight Log)"
        else do
            putStrLn $ "   Found " ++ show (length history) ++ " events in the Black Box:"
            mapM_ (\p -> do
                putStrLn "   --- EVENT ---"
                printPath "   " p
                ) history
    
    putStrLn "\n============================================"
    
    _ <- tryIO "sensor_core.txt"
    _ <- tryIO "sensor_turbine.txt"
    return ()
  where
    tryIO f = Prelude.writeFile f ""