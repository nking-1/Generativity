module Demos.Reactor where

import Control.Monad.Unravel
import Control.Monad.Unravel.SafeIO
import Data.Unravel.Universe
import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)

data ReactorState = ReactorState { temp :: Int, power :: Int } deriving (Show)

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
    return $ state { temp = temp state + 10, power = power state + efficiency }

runReactorDemo :: IO ()
runReactorDemo = do
    putStrLn "⚡ REACTOR DEMO STARTING..."
    liftIO $ writeFile "sensor_core.txt" "50"    
    liftIO $ writeFile "sensor_turbine.txt" "0"  
    
    let sim = foldM (\s f -> shield (controlLoop s f) s) (ReactorState 300 0) sensorFiles
    (res, u) <- runUnravelT sim
    
    printResult res u
    cleanup
  where
    cleanup = do
        _ <- tryIO "sensor_core.txt"
        _ <- tryIO "sensor_turbine.txt"
        return ()
    tryIO f = Prelude.writeFile f ""

printResult :: Show a => UResult a -> Universe -> IO ()
printResult res u = do
    putStrLn $ "Result: " ++ show res
    putStrLn $ "Entropy: " ++ show (getS u)
    putStrLn $ "Action:  " ++ show (getLagrangian u)
    let history = reconstruct (boundaryValue u)
    putStrLn $ "Events:  " ++ show (length history)