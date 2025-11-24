-- TestUnravelClean.hs
module Main where

import qualified UnravelClean as UC
import Prelude

main :: IO ()
main = do
  putStrLn "=== TESTING UNRAVELED OMEGA VEIL ==="
  
  -- Test basic evaluation
  putStrLn "\n--- Basic Evaluation ---"
  print (UC.eval_default (UC.EAdd (UC.ENum 5) (UC.ENum 3)))
  print (UC.eval_default (UC.EDiv (UC.ENum 10) (UC.ENum 0)))  -- Should be VVoid
  print (UC.eval_default (UC.EDefault (UC.EDiv (UC.ENum 10) (UC.ENum 0)) (UC.ENum 42)))
  
  -- Test variables
  putStrLn "\n--- Variable Evaluation ---"
  print (UC.evalV_empty UC.simple_let)  -- Should be VNum 15
  print (UC.evalV_empty UC.nested_let)  -- Should be VNum 30
  print (UC.evalV_empty UC.complex_with_vars)  -- Should be VNum 42
  
  -- Test thermodynamic evaluation
  putStrLn "\n--- Thermodynamic Evaluation ---"
  let (v1, u1) = UC.run_thermo UC.demo_division_chain
  putStrLn ("Result: " ++ show v1)
  putStrLn ("Universe: " ++ show u1)
  
  let (v2, u2) = UC.run_thermo UC.demo_entropy
  putStrLn ("\nEntropy demo result: " ++ show v2)
  putStrLn ("Total entropy: " ++ show (UC.total_entropy u2))
  putStrLn ("Time steps: " ++ show (UC.time_step u2))
  putStrLn ("Void count: " ++ show (UC.void_count u2))
  
  -- Test chaos generator
  putStrLn "\n--- Chaos Generator ---"
  let (v3, u3) = UC.run_thermo (UC.chaos_generator 3)
  putStrLn ("Chaos(3) entropy: " ++ show (UC.total_entropy u3))
  
  -- Test heat death
  putStrLn "\n--- Heat Death Check ---"
  putStrLn ("Is u3 heat death? " ++ show (UC.is_heat_death u3))
  
  let (v4, u4) = UC.run_thermo (UC.chaos_generator 50)
  putStrLn ("Chaos(50) entropy: " ++ show (UC.total_entropy u4))
  putStrLn ("Is u4 heat death? " ++ show (UC.is_heat_death u4))
  
  putStrLn "\n✅ All tests complete!"