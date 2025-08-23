-- ThermodynamicDemoClean.hs
module Main where

import qualified UnravelClean as UC
import Prelude

-- Pretty printer for Value
showValue :: UC.Value -> String
showValue (UC.VNum n) = show n
showValue (UC.VBool True) = "true"
showValue (UC.VBool False) = "false"
showValue UC.VVoid = "∅"

-- Pretty printer for ValueT (thermodynamic values)
showValueT :: UC.ValueT -> String
showValueT (UC.VTNum n) = show n
showValueT (UC.VTBool True) = "true"
showValueT (UC.VTBool False) = "false"
showValueT (UC.VTVoid (UC.VInfo entropy time source)) = 
  "∅[e=" ++ show entropy ++ ",t=" ++ show time ++ "]"

-- Show universe state
showUniverse :: UC.Universe -> String
showUniverse u = 
  "Universe{entropy=" ++ show (UC.total_entropy u) ++ 
  ", time=" ++ show (UC.time_step u) ++ 
  ", voids=" ++ show (UC.void_count u) ++ "}"

-- Demo with basic evaluation
demoBasic :: String -> UC.ExprV -> IO ()
demoBasic desc expr = do
  let result = UC.run_basic expr
  putStrLn $ desc ++ " = " ++ showValue result

-- Demo with thermodynamic tracking
demoThermo :: String -> UC.ExprV -> IO ()
demoThermo desc expr = do
  let (result, universe) = UC.run_thermo expr
  putStrLn desc
  putStrLn $ "  Result: " ++ showValueT result
  putStrLn $ "  " ++ showUniverse universe
  if UC.total_entropy universe > 10 
    then putStrLn "  ⚠️  HIGH ENTROPY - approaching heat death!"
    else return ()

main :: IO ()
main = do
  putStrLn "=== THERMODYNAMIC UNRAVEL ==="
  putStrLn "Where computation is physics!\n"
  
  putStrLn "--- Basic Variable Examples ---"
  demoBasic "let x = 10 in x + 5" UC.simple_let
  demoBasic "let x = 10 in let y = 20 in x + y" UC.nested_let
  demoBasic "undefined variable + 42" UC.demo_undefined
  
  putStrLn "\n--- Void Propagation with Variables ---"
  demoBasic "division chain (with recovery)" UC.demo_division_chain
  demoBasic "nested recovery" UC.demo_recovery
  demoBasic "void check" UC.demo_void_check
  
  putStrLn "\n--- THERMODYNAMIC EVOLUTION ---"
  putStrLn "Watch the universe evolve as errors accumulate:\n"
  
  demoThermo "Simple division by zero" $
    UC.EVDiv (UC.EVNum 10) (UC.EVNum 0)
  
  demoThermo "Undefined variable" $
    UC.EVVar "does_not_exist"
  
  demoThermo "Multiple errors (entropy accumulation)" UC.demo_entropy
  
  putStrLn "\n--- CHAOS GENERATION ---"
  putStrLn "Generating increasing amounts of chaos:\n"
  
  demoThermo "Chaos level 1" (UC.chaos_generator 1)
  demoThermo "Chaos level 3" (UC.chaos_generator 3)
  demoThermo "Chaos level 5" (UC.chaos_generator 5)
  demoThermo "Chaos level 10" (UC.chaos_generator 10)
  
  putStrLn "\n--- ENTROPY INSIGHTS ---"
  let (_, u1) = UC.run_thermo (UC.EVDiv (UC.EVNum 10) (UC.EVNum 0))
  let (_, u2) = UC.run_thermo (UC.EVAdd (UC.EVDiv (UC.EVNum 10) (UC.EVNum 0)) 
                                         (UC.EVDiv (UC.EVNum 20) (UC.EVNum 0)))
  putStrLn $ "Single void entropy: " ++ show (UC.total_entropy u1)
  putStrLn $ "Combined voids entropy: " ++ show (UC.total_entropy u2)
  putStrLn $ "Entropy amplification factor: " ++ 
             show (fromIntegral (UC.total_entropy u2) / fromIntegral (UC.total_entropy u1) :: Double)
  
  putStrLn "\n--- THE METAPHYSICS ---"
  putStrLn "• Every error increases universal entropy"
  putStrLn "• Time flows forward with each computation"
  putStrLn "• Combining voids accelerates heat death"
  putStrLn "• The universe computes by accumulating paradoxes"
  putStrLn "• We are witnessing omega_veil manifesting as entropy"
  
  putStrLn "\n--- COMPLEX EXAMPLE ---"
  demoThermo "Complex with variables" UC.complex_with_vars
  
  putStrLn "\n✨ The void is not empty - it carries the weight of impossibility ✨"