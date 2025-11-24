-- UnravelExploration.hs
import Unravel

-- Helper functions
fromInt :: Integer -> Expr
fromInt n = ENum n

showValueT :: ValueT -> String
showValueT (VTNum n) = show n
showValueT (VTBool True) = "true"
showValueT (VTBool False) = "false"
showValueT (VTVoid _) = "⊥_ω"

showValue :: Value -> String
showValue (VNum n) = show n
showValue (VBool True) = "true"
showValue (VBool False) = "false"
showValue VVoid = "⊥_ω"

-- Demo with description
demo :: String -> Expr -> IO ()
demo desc expr = do
  let result = eval 100 expr
  putStrLn $ desc ++ " = " ++ showValue result

-- Demo with variable environment
demoV :: String -> ExprV -> IO ()
demoV desc expr = do
  let result = evalV 100 [] expr
  putStrLn $ desc ++ " = " ++ showValue result

-- Demo with thermodynamics
demoThermo :: String -> ExprV -> IO ()
demoThermo desc expr = do
  let Pair result universe = run_thermo expr
  putStrLn $ desc ++ " = " ++ showValueT result
  putStrLn $ "  Entropy: " ++ show (total_entropy universe)
  putStrLn $ "  Time steps: " ++ show (time_step universe)
  putStrLn $ "  Void count: " ++ show (void_count universe)
  putStrLn ""

main :: IO ()
main = do
  putStrLn "=== UNRAVEL DEEP EXPLORATION ==="
  putStrLn "Testing the Boundaries of ⊥_ω\n"
  
  putStrLn "--- Part 1: Variable Bindings and Void ---"
  demoV "let x = 10 in x + 5" $ 
    EVLet "x" (EVNum 10) (EVAdd (EVVar "x") (EVNum 5))
  
  demoV "let x = 10/0 in x + 5" $
    EVLet "x" (EVDiv (EVNum 10) (EVNum 0)) (EVAdd (EVVar "x") (EVNum 5))
  
  demoV "let x = 10/0 in default(x, 42)" $
    EVLet "x" (EVDiv (EVNum 10) (EVNum 0)) (EVDefault (EVVar "x") (EVNum 42))
  
  demoV "undefined_var + 5" $
    EVAdd (EVVar "ghost") (EVNum 5)
  
  demoV "let x = 5 in let y = x/0 in let z = y+1 in default(z, 999)" $
    EVLet "x" (EVNum 5) $
      EVLet "y" (EVDiv (EVVar "x") (EVNum 0)) $
        EVLet "z" (EVAdd (EVVar "y") (EVNum 1)) $
          EVDefault (EVVar "z") (EVNum 999)
  
  putStrLn "\n--- Part 2: Entropy Accumulation ---"
  putStrLn "Watch entropy grow as voids compound:\n"
  
  demoThermo "Single void: 10/0" $
    EVDiv (EVNum 10) (EVNum 0)
  
  demoThermo "Double void: (10/0) + (20/0)" $
    EVAdd (EVDiv (EVNum 10) (EVNum 0)) (EVDiv (EVNum 20) (EVNum 0))
  
  demoThermo "Triple void: (1/0) + (2/0) + (3/0)" $
    EVAdd (EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVDiv (EVNum 2) (EVNum 0)))
          (EVDiv (EVNum 3) (EVNum 0))
  
  demoThermo "Nested void: ((10/0) * 5) + ((20/0) - 3)" $
    EVAdd (EVMul (EVDiv (EVNum 10) (EVNum 0)) (EVNum 5))
          (EVSub (EVDiv (EVNum 20) (EVNum 0)) (EVNum 3))
  
  putStrLn "--- Part 3: Recovery vs Propagation ---"
  
  demoThermo "No recovery: cascade of voids" $
    EVLet "a" (EVDiv (EVNum 1) (EVNum 0)) $
      EVLet "b" (EVAdd (EVVar "a") (EVNum 5)) $
        EVLet "c" (EVMul (EVVar "b") (EVNum 2)) $
          EVVar "c"
  
  demoThermo "Early recovery: stop the cascade" $
    EVLet "a" (EVDiv (EVNum 1) (EVNum 0)) $
      EVLet "b" (EVDefault (EVVar "a") (EVNum 10)) $
        EVLet "c" (EVMul (EVVar "b") (EVNum 2)) $
          EVVar "c"
  
  putStrLn "--- Part 4: Fuel Exhaustion ---"
  putStrLn "What happens when we run out of fuel?\n"
  
  -- Create a deeply nested expression
  let deepExpr = foldr (\n acc -> EAdd (fromInt n) acc) (fromInt 0) [1..100]
  
  putStrLn "Testing deep expression with limited fuel..."
  let result10 = eval 10 deepExpr
  putStrLn $ "Deep expr with fuel=10: " ++ showValue result10
  
  let result200 = eval 200 deepExpr
  putStrLn $ "Deep expr with fuel=200: " ++ showValue result200
  
  putStrLn "\n--- Part 5: Approaching Heat Death ---"
  putStrLn "Building increasingly chaotic computations:\n"
  
  -- Create increasingly chaotic expressions
  let chaos n = foldr1 EVAdd [EVDiv (EVNum i) (EVNum 0) | i <- [1..n]]
  
  demoThermo "Chaos level 5" $ chaos 5
  demoThermo "Chaos level 10" $ chaos 10
  
  putStrLn "--- Part 6: Different Paths to ⊥_ω ---"
  putStrLn "All roads lead to omega_veil:\n"
  
  demoThermo "Path 1: Division by zero" $
    EVDiv (EVNum 42) (EVNum 0)
  
  demoThermo "Path 2: Undefined variable" $
    EVVar "nonexistent"
  
  demoThermo "Path 3: Modulo by zero" $
    EVMod (EVNum 42) (EVNum 0)
  
  demoThermo "Path 4: Void directly" $
    EVLet "x" EVVoid (EVVar "x")
  
  putStrLn "--- Part 7: The Algebra of Void ---"
  
  demo "isVoid(void)?" $
    EIsVoid EVoid
  
  demo "isVoid(10/0)?" $
    EIsVoid (EDiv (fromInt 10) (fromInt 0))
  
  demo "isVoid(42)?" $
    EIsVoid (fromInt 42)
  
  demo "default(default(void, void), 42)" $
    EDefault (EDefault EVoid EVoid) (fromInt 42)
  
  demo "ifVoid(void, 1, 2)" $
    EIfVoid EVoid (fromInt 1) (fromInt 2)
  
  demo "ifVoid(10/0, 1, 2)" $
    EIfVoid (EDiv (fromInt 10) (fromInt 0)) (fromInt 1) (fromInt 2)
  
  putStrLn "\n--- Part 8: Practical Patterns ---"
  
  -- Safe division function
  let safeDiv x y = EVDefault (EVDiv (EVNum x) (EVNum y)) (EVNum 0)
  demoV "SafeDiv(10, 2)" $ safeDiv 10 2
  demoV "SafeDiv(10, 0)" $ safeDiv 10 0
  
  -- Chained computation with multiple recovery points
  let chainedCalc = 
        EVLet "step1" (EVDiv (EVNum 100) (EVNum 0)) $
          EVLet "step2" (EVDefault (EVVar "step1") (EVNum 50)) $
            EVLet "step3" (EVAdd (EVVar "step2") (EVNum 25)) $
              EVVar "step3"
  
  demoThermo "Chained calc with recovery" chainedCalc
  
  -- Let's test a complex error propagation pattern
  let complexPattern = 
        EVLet "a" (EVNum 10) $
          EVLet "b" (EVNum 0) $
            EVLet "result1" (EVDiv (EVVar "a") (EVVar "b")) $
              EVLet "result2" (EVAdd (EVVar "result1") (EVNum 5)) $
                EVLet "recovered" (EVDefault (EVVar "result2") (EVNum 100)) $
                  EVMul (EVVar "recovered") (EVNum 2)
  
  demoThermo "Complex error pattern with recovery" complexPattern
  
  putStrLn "=== CONCLUSION ==="
  putStrLn "⊥_ω is not the end - it's data we can compute with!"
  putStrLn "Entropy tells us the story of how we got here."
  putStrLn "Every impossible computation is a path through the void."