module Demos.DataScience where

import Control.Monad.Unravel
import Control.Monad.Unravel.SafeIO
import Data.Unravel.Universe
import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)
import Data.List (lines)

-- | A Dirty Data Processing Pipeline
-- Goal: Calculate average value from a messy CSV
-- Format: ID,Value
runDataScienceDemo :: IO ()
runDataScienceDemo = do
    putStrLn "📊 DATA SCIENCE DEMO STARTING..."
    
    -- Create a dummy dirty CSV
    let csvData = unlines 
            [ "1,100"
            , "2,200"
            , "3,invalid" -- Parse Error
            , "4,0"       -- Zero (might cause div error if used as denominator)
            , "5,"        -- Missing value
            , "6,300"
            ]
    writeFile "data.csv" csvData

    (res, u) <- runUnravelT (processFile "data.csv")
    
    putStrLn "\n--- DATA QUALITY REPORT ---"
    case res of
        Valid avg -> putStrLn $ "✅ Computed Average: " ++ show avg
        Invalid _ -> putStrLn "❌ Pipeline Failed"
        
    putStrLn $ "Total Rows Processed: " ++ show (mass u)
    putStrLn $ "Data Entropy (S):     " ++ show (getS u)
    putStrLn $ "Pipeline Action (L):  " ++ show (getLagrangian u)
    
    let quality = 1.0 - (getS u / fromIntegral (mass u))
    putStrLn $ "Dataset Quality Score: " ++ show quality

-- The Pipeline
processFile :: String -> UnravelT IO Int
processFile filename = do
    content <- safeIO $ readFile filename
    let rows = lines content
    
    -- Process rows. 
    -- We map 'parseRow' over them. If a row fails, 'shield' returns Nothing.
    -- We then filter Nothings and compute average.
    
    validValues <- foldM (\acc row -> do
        -- Attempt to parse and validate row
        -- If fails, return acc (skip row)
        shield (do
            val <- parseRow row
            work 1 -- Successful parse counts as mass
            return (val : acc)
          ) acc
      ) [] rows
      
    -- Compute Average
    let total = sum validValues
    let count = length validValues
    
    -- Safe Division (handles case where all rows fail)
    avg <- safeDiv total count
    return avg

parseRow :: String -> UnravelT IO Int
parseRow row = do
    -- Manual CSV parsing (risky!)
    let parts = split ',' row
    if length parts < 2 
       then crumble (LogicError $ "Malformed Row: " ++ row)
       else do
           let valStr = parts !! 1
           -- We try to read. If read fails, it throws exception -> safeIO catches it
           val <- safeIO $ return (read valStr :: Int)
           return val

split :: Char -> String -> [String]
split _ "" = [""]
split delim s = 
    let (h, t) = break (== delim) s
    in h : case t of
            "" -> []
            (_:t') -> split delim t'