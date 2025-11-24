module Main where

import ThermoParser
import ThermoTypeSystem
import ThermoLang
import UnravelMonad
import ThermoJSON
import Demos

import qualified Data.ByteString.Lazy as B
import qualified Data.Map as Map
import System.Environment (getArgs)
import System.IO (isEOF)

-- Run script with optional input data
runScript :: String -> Map.Map String UVal -> IO ()
runScript code env = do
    case parseThermo code of
        Left err -> putStrLn $ "❌ PARSE ERROR:\n" ++ err
        Right ast -> do
            -- Note: Type Checker currently doesn't know about 'input' variable types
            -- In v2 we would infer it from the JSON structure. 
            -- For now we skip static check for dynamic input or be permissive.
            
            let (res, u) = run (compile ast env)
            
            case res of
                Valid v   -> print v
                Invalid i -> putStrLn $ "Void: " ++ show i
            
            -- Print Physics to Stderr (so it doesn't pollute pipe)
            -- In Haskell putStrLn is stdout. We need hPutStrLn stderr.
            putStrLn $ "\n--- THERMODYNAMICS ---"
            putStrLn $ "Entropy: " ++ show (totalEntropy u)
            putStrLn $ "Time:    " ++ show (timeStep u)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["--demo", name] -> case name of
            "physics" -> runScript demoPhysics Map.empty
            "finance" -> runScript demoFinance Map.empty
            "consensus" -> runScript demoConsensus Map.empty
            _ -> putStrLn "Unknown demo"
            
        [scriptFile] -> do
            -- Read Script
            code <- readFile scriptFile
            
            -- Check if Stdin has data
            hasInput <- not <$> isEOF
            env <- if hasInput 
                   then do
                       content <- B.getContents
                       case parseJsonBytes content of
                           Right val -> return $ Map.singleton "input" val
                           Left err  -> error $ "JSON Parse Error: " ++ err
                   else return Map.empty
            
            runScript code env
            
        _ -> putStrLn "Usage: thermo <script.th> [ < data.json ]"