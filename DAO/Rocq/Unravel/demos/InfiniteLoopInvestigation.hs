-- InfiniteLoopInvestigation.hs
import Unravel
import Prelude hiding (lookup)

showResult :: Value -> String
showResult (VNum n) = show n
showResult VVoid = "∅ (void)"
showResult (VBool b) = show b

main :: IO ()
main = do
  putStrLn "=== INVESTIGATING THE '1' MYSTERY ===\n"
  
  -- Original attempt
  putStrLn "--- Original 'infinite loop' ---"
  let original = EVLet "counter" (EVNum 0)
                   (EVLet "loop" (EVAdd (EVVar "counter") (EVNum 1))
                     (EVVar "loop"))
  putStrLn $ "Result: " ++ showResult (run_basic original)
  putStrLn "Theory: 'loop' is bound to (counter + 1) = 1, not a recursive reference\n"
  
  -- Test 1: What if we try actual self-reference in the binding?
  putStrLn "--- Test 1: Direct self-reference ---"
  let selfRef = EVLet "x" (EVVar "x") (EVVar "x")
  putStrLn $ "let x = x in x: " ++ showResult (run_basic selfRef)
  putStrLn "(x references itself before being defined → void?)\n"
  
  -- Test 2: Mutual recursion attempt
  putStrLn "--- Test 2: Mutual recursion ---"
  let mutual = EVLet "x" (EVVar "y")
                 (EVLet "y" (EVVar "x")
                   (EVVar "x"))
  putStrLn $ "let x = y, y = x in x: " ++ showResult (run_basic mutual)
  putStrLn "(x needs y, y needs x → both void?)\n"
  
  -- Test 3: What about incrementing self?
  putStrLn "--- Test 3: Self-increment ---"
  let selfInc = EVLet "n" (EVAdd (EVVar "n") (EVNum 1)) (EVVar "n")
  putStrLn $ "let n = n + 1 in n: " ++ showResult (run_basic selfInc)
  putStrLn "(n references itself in its own definition)\n"
  
  -- Test 4: Different counter values
  putStrLn "--- Test 4: Different counter values ---"
  let makeLoop n = EVLet "counter" (EVNum n)
                     (EVLet "loop" (EVAdd (EVVar "counter") (EVNum 1))
                       (EVVar "loop"))
  putStrLn $ "counter=5, loop=counter+1: " ++ showResult (run_basic (makeLoop 5))
  putStrLn $ "counter=42, loop=counter+1: " ++ showResult (run_basic (makeLoop 42))
  putStrLn "(Confirms: loop just evaluates to counter + 1)\n"
  
  -- Test 5: Nested let with same names
  putStrLn "--- Test 5: Variable shadowing ---"
  let shadow = EVLet "x" (EVNum 10)
                 (EVLet "x" (EVAdd (EVVar "x") (EVNum 5))
                   (EVVar "x"))
  putStrLn $ "let x = 10 in let x = x + 5 in x: " ++ showResult (run_basic shadow)
  putStrLn "(Inner x shadows outer x)\n"
  
  -- Test 6: Try to build actual recursion via default
  putStrLn "--- Test 6: Recursion via default ---"
  let recDefault = EVLet "f" (EVDefault (EVVar "f") (EVNum 0))
                     (EVAdd (EVVar "f") (EVNum 1))
  putStrLn $ "let f = default(f, 0) in f + 1: " ++ showResult (run_basic recDefault)
  putStrLn "(Does default on undefined variable work?)\n"
  
  -- Test 7: What about referencing non-existent variables?
  putStrLn "--- Test 7: Undefined variables ---"
  putStrLn $ "Just 'ghost': " ++ showResult (run_basic (EVVar "ghost"))
  putStrLn $ "ghost + 5: " ++ showResult (run_basic (EVAdd (EVVar "ghost") (EVNum 5)))
  
  putStrLn "\n=== CONCLUSION ===\n"
  putStrLn "The 'infinite loop' returns 1 because:"
  putStrLn "1. 'loop' is bound to the expression (counter + 1)"
  putStrLn "2. counter = 0, so loop = 0 + 1 = 1"
  putStrLn "3. No actual recursion occurs - just simple evaluation"
  putStrLn "4. True self-reference (let x = x) returns void"
  putStrLn "\nUnravel prevents recursion at the binding level!"