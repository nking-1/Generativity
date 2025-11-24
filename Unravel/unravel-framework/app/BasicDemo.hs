module Main where

import Control.Monad.Unravel
import Control.Monad.Unravel.SafeIO
import Data.Unravel.Universe

-- A "Risky" Business Logic Pipeline
-- It mixes IO, Math, and State updates.
pipeline :: String -> UnravelT IO Int
pipeline filename = do
    -- 1. Try to read a file (Might fail!)
    content <- safeIO $ readFile filename
    
    -- 2. Do some work based on content length
    let len = length content
    work 10
    
    -- 3. Dangerous Math (Might fail!)
    -- If len is 0, this divides by zero
    ratio <- safeDiv 1000 len
    
    -- 4. Log success (Only runs if previous steps were Valid)
    safeIO $ putStrLn $ "Processed " ++ filename ++ ", Ratio: " ++ show ratio
    
    return ratio

-- The Resilient Wrapper
-- We shield the pipeline so the program never crashes.
main :: IO ()
main = do
    putStrLn "🚀 Starting Unravel Framework Demo..."

    -- Run 1: Happy Path
    putStrLn "\n--- TEST 1: Valid File ---"
    -- Fix: use standard IO here
    writeFile "test.txt" "Hello World"
    (res1, u1) <- runUnravelT $ shield (pipeline "test.txt") 0
    printResult res1 u1

    -- Run 2: IO Failure (Missing File)
    putStrLn "\n--- TEST 2: Missing File (IO Error) ---"
    (res2, u2) <- runUnravelT $ shield (pipeline "missing.txt") (-1)
    printResult res2 u2

    -- Run 3: Logic Failure (Empty File -> DivByZero)
    putStrLn "\n--- TEST 3: Empty File (DivByZero) ---"
    -- Fix: use standard IO here
    writeFile "empty.txt" ""
    (res3, u3) <- runUnravelT $ shield (pipeline "empty.txt") (-2)
    printResult res3 u3

    putStrLn "\n✅ System survived all failures."

printResult :: Show a => UResult a -> Universe -> IO ()
printResult res u = do
    putStrLn $ "Result:  " ++ show res
    putStrLn $ "Entropy: " ++ show (structEntropy u + timeEntropy u)
    putStrLn $ "Mass:    " ++ show (mass u)
    putStrLn $ "Hologram:" ++ show (boundaryValue u)
    
    -- Simple check for reconstruction (using logic from previous versions)
    if boundaryValue u > 0 
       then putStrLn "-> Singularity Detected & Recorded."
       else putStrLn "-> Clean Execution."