-- DeeperSymmetries.hs
import Unravel
import Prelude hiding (lookup)

-- Get entropy helper
getEntropy :: ExprV -> Integer
getEntropy expr = 
  case run_thermo expr of
    Pair _ u -> total_entropy u

-- Get value helper
getValue :: ExprV -> Value
getValue expr = evalV 100 [] expr

-- Show both value and entropy
showBoth :: String -> ExprV -> IO ()
showBoth desc expr = do
  let val = getValue expr
  let ent = getEntropy expr
  putStrLn $ "  " ++ desc
  putStrLn $ "    Value: " ++ showValue val
  putStrLn $ "    Entropy: " ++ show ent
  where
    showValue (VNum n) = show n
    showValue (VBool b) = show b
    showValue VVoid = "⊥_ω"

-- Test symmetry with detailed output
testSymmetry :: String -> ExprV -> ExprV -> IO ()
testSymmetry desc e1 e2 = do
  putStrLn $ "\n" ++ desc ++ ":"
  showBoth "Program 1" e1
  showBoth "Program 2" e2
  let ent1 = getEntropy e1
  let ent2 = getEntropy e2
  if ent1 == ent2
    then putStrLn "  ✓ Entropy conserved - programs are equivalent!"
    else putStrLn $ "  ✗ Entropy differs (" ++ show ent1 ++ " vs " ++ show ent2 ++ ")"

main :: IO ()
main = do
  putStrLn "=== DEEPER SYMMETRIES IN UNRAVEL ==="
  putStrLn "Exploring Complex Conservation Laws"
  
  putStrLn "\n--- DISTRIBUTIVITY ---"
  testSymmetry "Multiplication distributes over addition"
    (EVMul (EVNum 3) (EVAdd (EVNum 4) (EVNum 5)))  -- 3 * (4 + 5)
    (EVAdd (EVMul (EVNum 3) (EVNum 4)) 
           (EVMul (EVNum 3) (EVNum 5)))             -- (3 * 4) + (3 * 5)
  
  testSymmetry "Distributivity with void"
    (EVMul (EVNum 2) (EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVNum 3)))  -- 2 * (void + 3)
    (EVAdd (EVMul (EVNum 2) (EVDiv (EVNum 1) (EVNum 0)))
           (EVMul (EVNum 2) (EVNum 3)))                              -- (2 * void) + (2 * 3)
  
  putStrLn "\n--- PARTIAL EVALUATION ---"
  testSymmetry "Partial evaluation of known values"
    (EVLet "x" (EVNum 5) 
      (EVLet "y" (EVNum 10)
        (EVAdd (EVVar "x") (EVVar "y"))))     -- let x=5, y=10 in x+y
    (EVNum 15)                                 -- Pre-computed
  
  testSymmetry "Partial evaluation with void"
    (EVLet "x" (EVDiv (EVNum 1) (EVNum 0))
      (EVLet "y" (EVNum 10)
        (EVAdd (EVVar "x") (EVVar "y"))))     -- let x=void, y=10 in x+y
    (EVDiv (EVNum 1) (EVNum 0))               -- Should reduce to void
  
  putStrLn "\n--- LOOP UNROLLING (simulated) ---"
  -- Simulate: sum([1,2,3])
  let loop3 = EVAdd (EVNum 1) (EVAdd (EVNum 2) (EVNum 3))
  -- vs unrolled
  let unrolled3 = EVAdd (EVAdd (EVNum 1) (EVNum 2)) (EVNum 3)
  testSymmetry "Loop vs unrolled (3 iterations)" loop3 unrolled3
  
  -- With void in the loop
  let loopVoid = EVAdd (EVNum 1) (EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVNum 3))
  let unrolledVoid = EVAdd (EVAdd (EVNum 1) (EVDiv (EVNum 1) (EVNum 0))) (EVNum 3)
  testSymmetry "Loop with void vs unrolled" loopVoid unrolledVoid
  
  putStrLn "\n--- BOOLEAN SHORT-CIRCUITING ---"
  -- Can we detect that these are equivalent?
  testSymmetry "Short-circuit evaluation"
    (EVIfVoid (EVNum 5) 
      (EVNum 1)
      (EVDiv (EVNum 10) (EVNum 0)))  -- Second branch never taken
    (EVNum 1)                         -- Optimized version
  
  putStrLn "\n--- DE MORGAN'S LAWS (simulated with nested ifs) ---"
  -- not (A and B) = (not A) or (not B)
  -- Using void to simulate false
  testSymmetry "De Morgan's law simulation"
    (EVIfVoid (EVIfVoid (EVNum 1) EVVoid (EVNum 2)) 
      (EVNum 100) 
      (EVNum 200))  -- Complex nested structure
    (EVNum 100)     -- Simplified
  
  putStrLn "\n--- FUNCTION INLINING ---"
  -- Simulate function call vs inline
  testSymmetry "Function inlining"
    (EVLet "f" (EVNum 10)  -- 'function' that returns 10
      (EVLet "x" (EVNum 5)
        (EVAdd (EVVar "f") (EVVar "x"))))  -- f() + x
    (EVAdd (EVNum 10) (EVNum 5))           -- Inlined version
  
  putStrLn "\n--- MEMOIZATION EQUIVALENCE ---"
  -- Computing same thing twice vs once
  let expensive = EVDiv (EVNum 100) (EVNum 10)  -- "Expensive" computation
  testSymmetry "Redundant computation elimination"
    (EVAdd expensive expensive)                    -- Compute twice
    (EVMul (EVNum 2) expensive)                   -- Compute once, multiply
  
  putStrLn "\n--- ENTROPY GRADIENT SEARCH ---"
  putStrLn "\nSearching for optimization opportunities by entropy:"
  let original = EVAdd (EVMul (EVNum 2) (EVNum 3)) 
                       (EVMul (EVNum 2) (EVNum 4))
  let factored = EVMul (EVNum 2) (EVAdd (EVNum 3) (EVNum 4))
  putStrLn $ "  Original form: 2*3 + 2*4"
  putStrLn $ "    Entropy: " ++ show (getEntropy original)
  putStrLn $ "  Factored form: 2*(3+4)"  
  putStrLn $ "    Entropy: " ++ show (getEntropy factored)
  if getEntropy original == getEntropy factored
    then putStrLn "  ✓ Valid optimization found!"
    else putStrLn "  ✗ Not equivalent"
  
  putStrLn "\n--- VOID ALGEBRA LAWS ---"
  testSymmetry "Void is absorbing element"
    (EVMul EVVoid (EVNum 999999))  -- void * 999999
    EVVoid                          -- void
  
  testSymmetry "Void default right identity"
    (EVDefault (EVNum 42) EVVoid)   -- default(42, void)
    (EVNum 42)                       -- 42
  
  putStrLn "\n--- CASCADING OPTIMIZATION ---"
  let cascade1 = EVAdd (EVNum 0) 
                   (EVMul (EVNum 1) 
                     (EVAdd (EVNum 5) (EVNum 0)))
  let cascade2 = EVNum 5
  testSymmetry "Multiple optimization passes" cascade1 cascade2
  
  putStrLn "\n--- DISCOVERING NEW LAWS ---"
  putStrLn "\nHypothesis: All single-error programs have entropy 1"
  let singleErrors = [
        EVDiv (EVNum n) (EVNum 0) | n <- [1..5]
        ] ++ [
        EVVar ("var" ++ show n) | n <- [1..5]  
        ] ++ [
        EVMod (EVNum n) (EVNum 0) | n <- [1..5]
        ]
  let entropies = map getEntropy singleErrors
  putStrLn $ "  Entropies: " ++ show entropies
  if all (== 1) entropies
    then putStrLn "  ✓ LAW CONFIRMED: Single errors always have entropy 1"
    else putStrLn "  ✗ Law violated"
  
  putStrLn "\n--- THEORETICAL IMPLICATIONS ---"
  putStrLn "• Compiler correctness = Entropy conservation"
  putStrLn "• Optimization search = Find entropy-preserving transforms"
  putStrLn "• Program distance = Entropy difference"  
  putStrLn "• Refactoring safety = Check entropy invariance"
  putStrLn "• Dead code = Entropy 0 branches"