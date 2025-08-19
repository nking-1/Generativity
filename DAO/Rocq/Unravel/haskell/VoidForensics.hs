-- VoidForensics.hs
import Unravel
import Prelude hiding (lookup)

-- Extract void source information
showVoidSource :: VoidSource -> String
showVoidSource (DivByZero n) = "DivByZero(" ++ show n ++ ")"
showVoidSource (ModByZero n) = "ModByZero(" ++ show n ++ ")"
showVoidSource (UndefinedVar s) = "UndefinedVar(\"" ++ s ++ "\")"
showVoidSource OutOfFuel = "OutOfFuel"
showVoidSource (TypeError s) = "TypeError(\"" ++ s ++ "\")"
showVoidSource (VoidPropagation v1 v2) = "VoidPropagation[" ++ showVoidInfo v1 ++ " + " ++ showVoidInfo v2 ++ "]"

showVoidInfo :: VoidInfo -> String
showVoidInfo (VInfo e t s) = "{e=" ++ show e ++ ",src=" ++ showVoidSource s ++ "}"

-- Analyze a computation result
analyzeResult :: Prod ValueT Universe -> IO ()
analyzeResult (Pair v u) = do
  case v of
    VTNum n -> putStrLn $ "  SUCCESS: " ++ show n
    VTBool b -> putStrLn $ "  SUCCESS: " ++ show b
    VTVoid info -> do
      putStrLn $ "  VOID DETECTED!"
      case info of
        VInfo e t s -> do
          putStrLn $ "    Entropy contribution: " ++ show e
          putStrLn $ "    Failure time: step " ++ show t
          putStrLn $ "    Root cause: " ++ showVoidSource s
  putStrLn $ "  Universe state: entropy=" ++ show (total_entropy u) ++ 
             ", time=" ++ show (time_step u) ++ 
             ", total_voids=" ++ show (void_count u)

-- Test calculations that fail in various ways
main :: IO ()
main = do
  putStrLn "=== VOID FORENSICS: Tracing Computational Failure ==="
  putStrLn "Watch how failures accumulate entropy and leave traces!\n"
  
  putStrLn "--- CALCULATION 1: Simple Division Chain ---"
  putStrLn "Computing: (100/10) + (50/5) + (20/0)"
  let calc1 = EVAdd (EVDiv (EVNum 100) (EVNum 10))
                    (EVAdd (EVDiv (EVNum 50) (EVNum 5))
                           (EVDiv (EVNum 20) (EVNum 0)))
  analyzeResult (run_thermo calc1)
  
  putStrLn "\n--- CALCULATION 2: Variable Dependencies ---"
  putStrLn "Computing: let x = 10/2, y = x/0, z = missing_var in x+y+z"
  let calc2 = EVLet "x" (EVDiv (EVNum 10) (EVNum 2))
                (EVLet "y" (EVDiv (EVVar "x") (EVNum 0))
                  (EVLet "z" (EVVar "missing_var")
                    (EVAdd (EVVar "x") (EVAdd (EVVar "y") (EVVar "z")))))
  analyzeResult (run_thermo calc2)
  
  putStrLn "\n--- CALCULATION 3: Cascading Failures ---"
  putStrLn "Computing: Multiple errors combining"
  let calc3 = EVAdd 
                (EVDiv (EVNum 100) (EVNum 0))  -- First void
                (EVAdd 
                  (EVMod (EVNum 50) (EVNum 0))  -- Second void
                  (EVVar "undefined"))           -- Third void
  analyzeResult (run_thermo calc3)
  
  putStrLn "\n--- CALCULATION 4: Deep Nesting Failure ---"
  putStrLn "Computing: Deeply nested calculation that fails partway"
  let calc4 = EVMul 
                (EVAdd (EVNum 5) (EVNum 3))  -- 8
                (EVDiv 
                  (EVAdd (EVNum 10) (EVNum 10))  -- 20
                  (EVSub (EVNum 5) (EVNum 5)))   -- 0 - causes div/0!
  analyzeResult (run_thermo calc4)
  
  putStrLn "\n--- CALCULATION 5: Mixed Type Errors ---"
  putStrLn "Computing: (true + 5) * (10 / 0)"
  let calc5 = EVMul
                (EVAdd (EVBool True) (EVNum 5))
                (EVDiv (EVNum 10) (EVNum 0))
  analyzeResult (run_thermo calc5)
  
  putStrLn "\n--- CALCULATION 6: Recovery Attempt ---"
  putStrLn "Computing: default(undefined_var, 10) + (20/0)"
  let calc6 = EVAdd
                (EVDefault (EVVar "not_found") (EVNum 10))
                (EVDiv (EVNum 20) (EVNum 0))
  analyzeResult (run_thermo calc6)
  
  putStrLn "\n--- ENTROPY ACCUMULATION ANALYSIS ---"
  
  -- Run a series of calculations to show entropy growth
  let simpleError = EVDiv (EVNum 1) (EVNum 0)
  let doubleError = EVAdd simpleError simpleError
  let tripleError = EVAdd doubleError simpleError
  
  let getEntropy expr = case run_thermo expr of Pair _ u -> total_entropy u
  
  putStrLn "Entropy growth pattern:"
  putStrLn $ "  1 error:  " ++ show (getEntropy simpleError) ++ " entropy"
  putStrLn $ "  2 errors: " ++ show (getEntropy doubleError) ++ " entropy"
  putStrLn $ "  3 errors: " ++ show (getEntropy tripleError) ++ " entropy"
  
  putStrLn "\n--- FAILURE TYPE DISTRIBUTION ---"
  
  -- Create different types of failures
  let failures = 
        [ ("Division by zero", EVDiv (EVNum 10) (EVNum 0))
        , ("Modulo by zero", EVMod (EVNum 10) (EVNum 0))
        , ("Undefined variable", EVVar "ghost")
        , ("Type error", EVAdd (EVBool True) (EVNum 5))
        , ("Propagated void", EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVNum 5))
        ]
  
  putStrLn "Different failure types and their entropy:"
  mapM_ (\(desc, expr) -> do
    let Pair v u = run_thermo expr
    putStrLn $ "  " ++ desc ++ ": entropy=" ++ show (total_entropy u)
    case v of
      VTVoid (VInfo _ _ src) -> putStrLn $ "    Source: " ++ showVoidSource src
      _ -> return ()
    ) failures
  
  putStrLn "\n--- FINAL INSIGHTS ---"
  putStrLn "• Each failure type leaves a unique fingerprint"
  putStrLn "• Entropy accumulates non-linearly when voids combine"
  putStrLn "• The universe tracks every computational sin"
  putStrLn "• Void carries complete failure forensics"
  putStrLn "• Time advances even through failure"
  putStrLn "\n✨ The void remembers everything! ✨"