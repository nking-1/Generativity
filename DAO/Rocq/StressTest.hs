-- StressTest.hs
import VoidLang
import Prelude hiding (lookup)

-- Helper to show results
showResult :: Value -> String
showResult (VNum n) = show n
showResult VVoid = "∅ (FORCED TERMINATION)"
showResult (VBool b) = show b

-- Helper to show thermodynamic results
showThermo :: Prod ValueT Universe -> String
showThermo (Pair v u) = 
  "Entropy: " ++ show (total_entropy u) ++ 
  ", Time: " ++ show (time_step u)

-- STRESS TEST 1: Try to build massive nested expression
massiveNesting :: Integer -> ExprV
massiveNesting 0 = EVNum 1
massiveNesting n = EVAdd (massiveNesting (n-1)) (massiveNesting (n-1))

-- STRESS TEST 2: Mutual "recursion" attempt via let bindings
mutualRecursion :: ExprV
mutualRecursion = 
  EVLet "f" (EVVar "g")  -- f tries to reference g
    (EVLet "g" (EVVar "f")  -- g tries to reference f
      (EVAdd (EVVar "f") (EVVar "g")))  -- Try to use both

-- STRESS TEST 3: Deep let nesting
deepLetNesting :: Integer -> ExprV
deepLetNesting 0 = EVNum 42
deepLetNesting n = 
  EVLet ("x" ++ show n) (EVNum n)
    (EVAdd (EVVar ("x" ++ show n)) (deepLetNesting (n-1)))

-- STRESS TEST 4: Exponential branching
exponentialBranching :: Integer -> ExprV
exponentialBranching 0 = EVNum 1
exponentialBranching n =
  EVIfVoid (EVDiv (EVNum n) (EVNum n))  -- Always false (n/n = 1, not void)
    (exponentialBranching (n-1))  -- Never taken
    (EVAdd (exponentialBranching (n-1)) (exponentialBranching (n-1)))  -- Doubles each time

-- STRESS TEST 5: Try to exhaust fuel with arithmetic
arithmeticBomb :: Integer -> ExprV
arithmeticBomb n = foldl EVAdd (EVNum 0) [EVNum i | i <- [1..n]]

-- STRESS TEST 6: Maximum void generation
voidBomb :: Integer -> ExprV
voidBomb 0 = EVDiv (EVNum 1) (EVNum 0)
voidBomb n = EVAdd (voidBomb (n-1)) (voidBomb (n-1))

-- STRESS TEST 7: Attempting "while true" pattern
whileTrue :: ExprV
whileTrue = 
  EVLet "condition" (EVBool True)
    (EVLet "loop" (EVIfVoid (EVVar "condition") 
                    (EVNum 0)  -- Exit on void (never happens)
                    (EVVar "loop"))  -- Try to loop
      (EVVar "loop"))

-- Test with different fuel amounts
testWithFuel :: Integer -> String -> ExprV -> IO ()
testWithFuel fuel desc expr = do
  let result = evalV fuel [] expr
  putStrLn $ desc ++ " (fuel=" ++ show fuel ++ "): " ++ showResult result

-- Test thermodynamics under stress
testThermo :: String -> ExprV -> IO ()
testThermo desc expr = do
  let result = run_thermo expr
  putStrLn $ desc ++ ": " ++ showThermo result

main :: IO ()
main = do
  putStrLn "=== STRESS TESTING VOIDLANG'S TERMINATION ==="
  putStrLn "No matter what we try, everything MUST terminate!\n"
  
  putStrLn "--- TEST 1: MASSIVE NESTING ---"
  putStrLn "Building expressions with exponential growth..."
  testWithFuel 10 "Nesting depth 5" (massiveNesting 5)
  testWithFuel 100 "Nesting depth 8" (massiveNesting 8)
  testWithFuel 1000 "Nesting depth 10" (massiveNesting 10)
  testWithFuel 1000 "Nesting depth 15" (massiveNesting 15)
  putStrLn "  ↑ Even with 1000 fuel, deep nesting exhausts it!\n"
  
  putStrLn "--- TEST 2: MUTUAL RECURSION ATTEMPT ---"
  testWithFuel 100 "Mutual recursion" mutualRecursion
  putStrLn "  ↑ Can't create cycles through let bindings!\n"
  
  putStrLn "--- TEST 3: DEEP LET NESTING ---"
  testWithFuel 100 "100 nested lets" (deepLetNesting 100)
  testWithFuel 1000 "200 nested lets" (deepLetNesting 200)
  putStrLn "  ↑ Fuel limits evaluation depth!\n"
  
  putStrLn "--- TEST 4: EXPONENTIAL BRANCHING ---"
  testWithFuel 100 "2^5 branches" (exponentialBranching 5)
  testWithFuel 1000 "2^7 branches" (exponentialBranching 7)
  testWithFuel 10000 "2^10 branches" (exponentialBranching 10)
  putStrLn "  ↑ Even 10000 fuel can't handle exponential growth!\n"
  
  putStrLn "--- TEST 5: ARITHMETIC BOMBARDMENT ---"
  testWithFuel 100 "Sum of 50 numbers" (arithmeticBomb 50)
  testWithFuel 100 "Sum of 200 numbers" (arithmeticBomb 200)
  putStrLn "  ↑ Too many operations exhaust fuel!\n"
  
  putStrLn "--- TEST 6: VOID BOMB (THERMODYNAMIC STRESS) ---"
  testThermo "Single void" (voidBomb 0)
  testThermo "2 voids combined" (voidBomb 1)
  testThermo "4 voids combined" (voidBomb 2)
  testThermo "8 voids combined" (voidBomb 3)
  putStrLn "  ↑ Watch entropy explode!\n"
  
  putStrLn "--- TEST 7: 'WHILE TRUE' ATTEMPT ---"
  testWithFuel 100 "While true pattern" whileTrue
  putStrLn "  ↑ Can't create infinite loops!\n"
  
  putStrLn "--- THE ULTIMATE TEST: VARY FUEL ---"
  let bigExpr = exponentialBranching 20
  putStrLn "Same expression, different fuel amounts:"
  testWithFuel 1 "Fuel=1" bigExpr
  testWithFuel 10 "Fuel=10" bigExpr
  testWithFuel 100 "Fuel=100" bigExpr
  testWithFuel 1000 "Fuel=1000" bigExpr
  testWithFuel 10000 "Fuel=10000" bigExpr
  putStrLn "  ↑ ALL terminate, just at different points!\n"
  
  putStrLn "=== CONCLUSION ==="
  putStrLn "• NO expression can run forever"
  putStrLn "• Fuel is a HARD LIMIT enforced by the evaluator"
  putStrLn "• Complex expressions just exhaust fuel faster"
  putStrLn "• The universe (evaluator) ALWAYS wins"
  putStrLn "• Termination is not a choice - it's a LAW"
  putStrLn "\n✨ The halting problem doesn't exist here - everything halts! ✨"