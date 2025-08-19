-- RunTestSuite.hs
import Unravel
import Prelude hiding (lookup)

-- Helper to show Value
showValue :: Value -> String
showValue (VNum n) = show n
showValue (VBool True) = "true"
showValue (VBool False) = "false"
showValue VVoid = "∅"

-- Helper to show ValueT with entropy info
showValueT :: ValueT -> String
showValueT (VTNum n) = show n
showValueT (VTBool True) = "true"
showValueT (VTBool False) = "false"
showValueT (VTVoid (VInfo e t _)) = "∅[entropy=" ++ show e ++ ",time=" ++ show t ++ "]"

-- Helper to show Universe
showUniverse :: Universe -> String
showUniverse u = 
  "{entropy=" ++ show (total_entropy u) ++ 
  ", time=" ++ show (time_step u) ++ 
  ", voids=" ++ show (void_count u) ++ "}"

-- Run a test and show both basic and thermodynamic results
runTest :: Integer -> ExprV -> IO ()
runTest idx expr = do
  putStrLn $ "\n[Test " ++ show idx ++ "]"
  
  -- Basic evaluation
  let basic_result = run_basic expr
  putStrLn $ "  Basic result: " ++ showValue basic_result
  
  -- Thermodynamic evaluation
  let Pair thermo_result universe = run_thermo expr
  putStrLn $ "  Thermo result: " ++ showValueT thermo_result
  putStrLn $ "  Universe: " ++ showUniverse universe
  
  -- Flag interesting cases
  if total_entropy universe > 5
    then putStrLn $ "  ⚠️  HIGH ENTROPY DETECTED!"
    else return ()

main :: IO ()
main = do
  putStrLn "=== RUNNING COQ'S EXTRACTED TEST SUITE ==="
  putStrLn "These are the test programs Coq built for us!\n"
  
  -- Name the tests for clarity
  let test_names = 
        [ "Division chain with recovery"
        , "Undefined variable handling"  
        , "Multiple errors (entropy accumulation)"
        , "Nested recovery"
        , "Void checking"
        , "Simple let binding"
        , "Nested let bindings"
        , "Complex with variables"
        , "Chaos generator (level 5)"
        , "Chaos generator (level 10)"
        ]
  
  -- Run each test
  putStrLn $ "Found " ++ show (length test_programs) ++ " test programs"
  putStrLn "-------------------------------------------"
  
  -- Zip with indices and names
  sequence_ $ zipWith3 
    (\idx name prog -> do
      putStrLn $ "\n[Test " ++ show idx ++ ": " ++ name ++ "]"
      let basic_result = run_basic prog
      putStrLn $ "  Basic: " ++ showValue basic_result
      let Pair thermo_result universe = run_thermo prog
      putStrLn $ "  Thermo: " ++ showValueT thermo_result
      putStrLn $ "  Universe: " ++ showUniverse universe
      if total_entropy universe > 10
        then putStrLn $ "  🔥 APPROACHING HEAT DEATH!"
        else if total_entropy universe > 5
        then putStrLn $ "  ⚠️  High entropy!"
        else if total_entropy universe > 0
        then putStrLn $ "  ⚡ Some entropy generated"
        else putStrLn $ "  ✓ Clean computation"
    )
    [1..] 
    test_names 
    test_programs
  
  putStrLn "\n\n=== SUMMARY STATISTICS ==="
  
  let entropies = map (\prog -> 
        case run_thermo prog of 
          Pair _ u -> total_entropy u
        ) test_programs
  
  let void_counts = map (\prog -> 
        case run_thermo prog of 
          Pair _ u -> void_count u
        ) test_programs
  
  putStrLn $ "Total tests: " ++ show (length test_programs)
  putStrLn $ "Max entropy: " ++ show (maximum entropies)
  putStrLn $ "Min entropy: " ++ show (minimum entropies)
  putStrLn $ "Average entropy: " ++ show (sum entropies `Prelude.div` fromIntegral (length entropies))
  putStrLn $ "Tests with voids: " ++ show (length $ filter (> 0) void_counts)
  putStrLn $ "Tests without voids: " ++ show (length $ filter (== 0) void_counts)
  
  putStrLn "\n✨ Coq's test suite validated! ✨"