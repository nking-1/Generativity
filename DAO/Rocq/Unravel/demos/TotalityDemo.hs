-- TotalityDemo.hs
import Unravel
import Prelude hiding (lookup)

-- Helper to show results
showResult :: Value -> String
showResult (VNum n) = show n
showResult VVoid = "∅ (computation exhausted)"
showResult (VBool b) = show b

-- ATTEMPTING INFINITE LOOPS

-- This LOOKS like an infinite loop but isn't!
notActuallyInfinite :: ExprV
notActuallyInfinite = 
  EVLet "counter" (EVNum 0)
    (EVLet "loop" (EVAdd (EVVar "counter") (EVNum 1))  
      (EVVar "loop"))  -- Just returns counter + 1 = 1

-- TRUE self-reference attempt (returns void)
actualSelfReference :: ExprV
actualSelfReference = 
  EVLet "x" (EVVar "x")  -- x refers to itself before being defined
    (EVVar "x")           -- Returns void!

-- Mutual recursion attempt (also void)
mutualRecursion :: ExprV
mutualRecursion =
  EVLet "x" (EVVar "y")
    (EVLet "y" (EVVar "x")
      (EVVar "x"))  -- Both undefined, returns void

-- Factorial with bounded recursion (pseudo-recursion via fuel)
factorial :: Integer -> ExprV
factorial n = factHelper n n
  where
    factHelper 0 acc = EVNum 1
    factHelper fuel 0 = EVNum 1  
    factHelper fuel n = 
      if fuel > 0
      then EVMul (EVNum n) (factHelper (fuel-1) (n-1))
      else EVVoid  -- Out of fuel!

-- Sum from 1 to n (bounded iteration)
sumTo :: Integer -> ExprV
sumTo n = sumHelper n 0
  where
    sumHelper 0 acc = EVNum acc
    sumHelper k acc = 
      EVAdd (EVNum k) (sumHelper (k-1) acc)

-- "While loop" that terminates via fuel
whileLoop :: Integer -> ExprV
whileLoop maxSteps = loop maxSteps 0
  where
    loop 0 acc = EVNum acc  -- Fuel exhausted, return result
    loop fuel acc = 
      EVIfVoid (EVDiv (EVNum 10) (EVNum 0))  -- Condition that creates void
        (EVNum acc)  -- Exit on void
        (loop (fuel-1) (acc+1))  -- Continue with less fuel

-- Fibonacci with bounded recursion
fibonacci :: Integer -> ExprV
fibonacci n = fibHelper n
  where
    fibHelper 0 = EVNum 0
    fibHelper 1 = EVNum 1
    fibHelper n = 
      if n > 20  -- Reasonable bound
      then EVVoid  -- Too large, return void
      else EVAdd (fibHelper (n-1)) (fibHelper (n-2))

-- List processing (simulated) with bounds
mapList :: Integer -> ExprV
mapList 0 = EVNum 0
mapList n = EVAdd (EVMul (EVNum n) (EVNum 2)) (mapList (n-1))

-- Server loop (simulated) - runs for fixed iterations
serverLoop :: Integer -> ExprV
serverLoop maxRequests = handleRequests maxRequests
  where
    handleRequests 0 = EVNum 0  -- Server shutdown
    handleRequests n = 
      EVLet "request" (EVNum n)
        (EVLet "response" (EVMul (EVVar "request") (EVNum 2))
          (EVAdd (EVVar "response") (handleRequests (n-1))))

main :: IO ()
main = do
  putStrLn "=== TOTALITY IN UNRAVEL ==="
  putStrLn "Everything terminates, even 'infinite' loops!\n"
  
  putStrLn "--- RECURSION ATTEMPTS ---"
  putStrLn $ "Looks infinite but isn't: " ++ showResult (run_basic notActuallyInfinite)
  putStrLn "  (Just evaluates to counter + 1 = 1)\n"
  
  putStrLn $ "True self-reference (let x = x): " ++ showResult (run_basic actualSelfReference)
  putStrLn "  (Variable undefined during own binding → void)\n"
  
  putStrLn $ "Mutual recursion attempt: " ++ showResult (run_basic mutualRecursion)
  putStrLn "  (Circular dependency → void)\n"
  
  putStrLn "--- BOUNDED RECURSION WORKS ---"
  putStrLn $ "factorial(5) = " ++ showResult (run_basic (factorial 5))
  putStrLn $ "factorial(10) = " ++ showResult (run_basic (factorial 10))
  putStrLn $ "fibonacci(8) = " ++ showResult (run_basic (fibonacci 8))
  putStrLn $ "sum(1..10) = " ++ showResult (run_basic (sumTo 10))
  
  putStrLn "\n--- PRACTICAL PATTERNS ---"
  putStrLn $ "Server handling 5 requests: " ++ showResult (run_basic (serverLoop 5))
  putStrLn $ "Mapping over 5 elements: " ++ showResult (run_basic (mapList 5))
  
  putStrLn "\n--- FUEL EXHAUSTION ---"
  -- These work because they're within fuel limits
  putStrLn $ "fibonacci(10) = " ++ showResult (run_basic (fibonacci 10))
  putStrLn $ "fibonacci(15) = " ++ showResult (run_basic (fibonacci 15))
  -- This might hit bounds
  putStrLn $ "fibonacci(25) = " ++ showResult (run_basic (fibonacci 25))
  
  putStrLn "\n--- Why Unravel is Total ---"
  putStrLn "• No recursive let bindings (self-reference = void)"
  putStrLn "• No fixpoint operator"
  putStrLn "• Fuel bounds all evaluation"
  putStrLn "• Void catches all failure modes"
  putStrLn "• Result: EVERY program terminates!"