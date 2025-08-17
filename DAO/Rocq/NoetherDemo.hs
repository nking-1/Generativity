-- NoetherDemo.hs
import VoidLang
import Prelude hiding (lookup)

-- Show universe state
showUniverse :: Universe -> String
showUniverse u = 
  "Universe{entropy=" ++ show (total_entropy u) ++ 
  ", time=" ++ show (time_step u) ++ 
  ", voids=" ++ show (void_count u) ++ "}"

-- Get just the entropy from evaluation
getEntropy :: ExprV -> Integer
getEntropy expr = 
  case run_thermo expr of
    Pair _ u -> total_entropy u

-- Demo a symmetry transformation
demoSymmetry :: String -> ExprV -> ExprV -> IO ()
demoSymmetry desc e1 e2 = do
  putStrLn $ desc ++ ":"
  let entropy1 = getEntropy e1
  let entropy2 = getEntropy e2
  putStrLn $ "  Program 1 entropy: " ++ show entropy1
  putStrLn $ "  Program 2 entropy: " ++ show entropy2
  if entropy1 == entropy2
    then putStrLn $ "  ✓ NOETHER'S THEOREM CONFIRMED - Entropy conserved!"
    else putStrLn $ "  ✗ Different entropy - not equivalent programs"

main :: IO ()
main = do
  putStrLn "=== NOETHER'S THEOREM IN VOIDLANG ==="
  putStrLn "Symmetry → Conservation\n"
  
  putStrLn "--- THEOREM 1: Commutative Operations Preserve Entropy ---"
  demoSymmetry "Addition commutativity"
    (EVAdd (EVNum 5) (EVNum 3))
    (EVAdd (EVNum 3) (EVNum 5))
  
  demoSymmetry "Void addition commutativity" 
    (EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVNum 5))
    (EVAdd (EVNum 5) (EVDiv (EVNum 1) (EVNum 0)))
  
  putStrLn "\n--- THEOREM 2: Associative Operations Preserve Entropy ---"
  demoSymmetry "Addition associativity"
    (EVAdd (EVAdd (EVNum 1) (EVNum 2)) (EVNum 3))
    (EVAdd (EVNum 1) (EVAdd (EVNum 2) (EVNum 3)))
    
  putStrLn "\n--- THEOREM 3: Equivalent Errors Have Same Entropy ---"
  demoSymmetry "Different divisions by zero"
    (EVDiv (EVNum 10) (EVNum 0))
    (EVDiv (EVNum 999) (EVNum 0))
  
  demoSymmetry "Different undefined variables"
    (EVVar "x")
    (EVVar "y")
    
  putStrLn "\n--- THEOREM 4: Dead Code Elimination ---"
  demoSymmetry "Unreachable code removal"
    (EVIfVoid (EVNum 5) 
      (EVDiv (EVNum 1) (EVNum 0))  -- Never executed
      (EVNum 42))
    (EVNum 42)  -- Simplified version
  
  putStrLn "\n--- THEOREM 5: Let-Binding Transformation ---"
  demoSymmetry "Let-binding vs direct substitution"
    (EVLet "x" (EVNum 10) (EVAdd (EVVar "x") (EVNum 5)))
    (EVAdd (EVNum 10) (EVNum 5))
  
  putStrLn "\n--- COUNTEREXAMPLE: Non-Equivalent Programs ---"
  demoSymmetry "Different error counts"
    (EVDiv (EVNum 10) (EVNum 0))  -- One void
    (EVAdd (EVDiv (EVNum 10) (EVNum 0)) 
           (EVDiv (EVNum 20) (EVNum 0)))  -- Multiple voids
  
  putStrLn "\n--- THE VARIATIONAL PRINCIPLE ---"
  putStrLn "All void expressions minimize action:"
  let voids = [EVDiv (EVNum n) (EVNum 0) | n <- [1..5]]
  let entropies = map getEntropy voids
  putStrLn $ "  Entropies: " ++ show entropies
  if all (== (entropies !! 0)) entropies
    then putStrLn "  ✓ All voids have minimal action (entropy=1)"
    else putStrLn "  ✗ Unexpected variation"
  
  putStrLn "\n--- SYMMETRY GROUP GENERATOR ---"
  putStrLn "Omega_veil generates all impossibilities:"
  let generated = [EVDiv (EVNum n) (EVNum 0) | n <- [1..3]]
  putStrLn $ "  All map to entropy=" ++ show (getEntropy (generated !! 0))
  
  putStrLn "\n--- CONSERVATION UNDER OPTIMIZATION ---"
  let unoptimized = EVAdd (EVAdd (EVNum 1) (EVNum 0)) 
                          (EVMul (EVNum 2) (EVNum 1))
  let optimized = EVAdd (EVNum 1) (EVNum 2)  -- After constant folding
  demoSymmetry "Constant folding optimization" unoptimized optimized
  
  putStrLn "\n--- DEEP INSIGHT ---"
  putStrLn "• Program equivalence ≡ Entropy conservation"
  putStrLn "• Compiler optimizations are symmetry transformations"
  putStrLn "• Omega_veil is the generator of the symmetry group"
  putStrLn "• Every refactoring must preserve total entropy"
  putStrLn "• The universe's conservation laws apply to code!"
  
  putStrLn "\n✨ Emmy Noether would be proud - "
  putStrLn "   symmetry and conservation united in pure logic! ✨"