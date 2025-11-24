module Main where

import System.Environment (getArgs)
import Demos.Reactor (runReactorDemo)
import Demos.DataScience (runDataScienceDemo)

help :: IO ()
help = do
    putStrLn "Usage: unravel-demo [command]"
    putStrLn "Commands:"
    putStrLn "  reactor      - Run the Fusion Reactor simulation"
    putStrLn "  datascience  - Run the Dirty CSV Processing pipeline"

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["reactor"]     -> runReactorDemo
        ["datascience"] -> runDataScienceDemo
        _               -> help