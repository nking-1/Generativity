-- ThermodynamicDemo.hs
import Unravel
import Prelude hiding (lookup)

-- Pretty printer for Value
showValue :: Value -> String
showValue (VNum n) = show n
showValue (VBool True) = "true"
showValue (VBool False) = "false"
showValue VVoid = "∅"

-- Pretty printer for ValueT (thermodynamic values)
showValueT :: ValueT -> String
showValueT (VTNum n) = show n
showValueT (VTBool True) = "true"
showValueT (VTBool False) = "false"
showValueT (VTVoid (VInfo entropy time source)) = 
  "∅[e=" ++ show entropy ++ ",t=" ++ show time ++ "]"

-- Show universe state
showUniverse :: Universe -> String
showUniverse u = 
  "Universe{entropy=" ++ show (total_entropy u) ++ 
  ", time=" ++ show (time_step u) ++ 
  ", voids=" ++ show (void_count u) ++ "}"

-- Demo with basic evaluation
demoBasic :: String -> ExprV -> IO ()
demoBasic desc expr = do
  let result = run_basic expr
  putStrLn $ desc ++ " = " ++ showValue result

-- Demo with thermodynamic tracking
demoThermo :: String -> ExprV -> IO ()
demoThermo desc expr = do
  let Pair result universe = run_thermo expr  -- Use Pair instead of tuple
  putStrLn $ desc
  putStrLn $ "  Result: " ++ showValueT result
  putStrLn $ "  " ++ showUniverse universe
  if total_entropy universe > 10 
    then putStrLn $ "  ⚠️  HIGH ENTROPY - approaching heat death!"
    else return ()

main :: IO ()
main = do
  putStrLn "=== THERMODYNAMIC UNRAVEL ==="
  putStrLn "Where computation is physics!\n"
  
  putStrLn "--- Basic Variable Examples ---"
  demoBasic "let x = 10 in x + 5" simple_let
  demoBasic "let x = 10 in let y = 20 in x + y" nested_let
  demoBasic "undefined variable + 42" demo_undefined
  
  putStrLn "\n--- Void Propagation with Variables ---"
  demoBasic "division chain (with recovery)" demo_division_chain
  demoBasic "nested recovery" demo_recovery
  demoBasic "void check" demo_void_check
  
  putStrLn "\n--- THERMODYNAMIC EVOLUTION ---"
  putStrLn "Watch the universe evolve as errors accumulate:\n"
  
  demoThermo "Simple division by zero" $
    EVDiv (EVNum 10) (EVNum 0)
  
  demoThermo "Undefined variable" $
    EVVar "does_not_exist"
  
  demoThermo "Multiple errors (entropy accumulation)" demo_entropy
  
  putStrLn "\n--- CHAOS GENERATION ---"
  putStrLn "Generating increasing amounts of chaos:\n"
  
  demoThermo "Chaos level 1" (chaos_generator 1)
  demoThermo "Chaos level 3" (chaos_generator 3)
  demoThermo "Chaos level 5" (chaos_generator 5)
  demoThermo "Chaos level 10" (chaos_generator 10)
  
  putStrLn "\n--- ENTROPY INSIGHTS ---"
  let Pair _ u1 = run_thermo (EVDiv (EVNum 10) (EVNum 0))
  let Pair _ u2 = run_thermo (EVAdd (EVDiv (EVNum 10) (EVNum 0)) 
                                     (EVDiv (EVNum 20) (EVNum 0)))
  putStrLn $ "Single void entropy: " ++ show (total_entropy u1)
  putStrLn $ "Combined voids entropy: " ++ show (total_entropy u2)
  putStrLn $ "Entropy amplification factor: " ++ 
             show (fromIntegral (total_entropy u2) / fromIntegral (total_entropy u1) :: Double)
  
  putStrLn "\n--- THE METAPHYSICS ---"
  putStrLn "• Every error increases universal entropy"
  putStrLn "• Time flows forward with each computation"
  putStrLn "• Combining voids accelerates heat death"
  putStrLn "• The universe computes by accumulating paradoxes"
  putStrLn "• We are witnessing omega_veil manifesting as entropy"
  
  putStrLn "\n--- COMPLEX EXAMPLE ---"
  demoThermo "Complex with variables" complex_with_vars
  
  putStrLn "\n✨ The void is not empty - it carries the weight of impossibility ✨"