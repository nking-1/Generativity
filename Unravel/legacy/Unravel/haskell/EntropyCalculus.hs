-- EntropyCalculus.hs
import Unravel
import Prelude hiding (lookup)

-- Helpers
showThermo :: String -> ExprV -> IO ()
showThermo desc expr = do
  let Pair result universe = run_thermo expr
  let entropy = total_entropy universe
  let time = time_step universe
  let voids = void_count universe
  putStrLn $ desc
  putStrLn $ "  Result: " ++ showValue result
  putStrLn $ "  Entropy: " ++ show entropy ++ ", Time: " ++ show time ++ ", Voids: " ++ show voids
  putStrLn ""

showValue :: ValueT -> String
showValue (VTNum n) = show n
showValue (VTBool b) = show b
showValue (VTVoid _) = "⊥_ω"

-- Build a void source
mkVoid :: ExprV
mkVoid = EVDiv (EVNum 1) (EVNum 0)

-- Build a pure value
mkPure :: Integer -> ExprV
mkPure n = EVNum n

main :: IO ()
main = do
  putStrLn "=== ENTROPY CALCULUS: EXPLORING THE FLOW ===\n"
  
  putStrLn "--- EXPERIMENT 1: Entropy Operators ---"
  putStrLn "How does each operator contribute to entropy?\n"
  
  showThermo "Pure addition: 5 + 3" $
    EVAdd (mkPure 5) (mkPure 3)
  
  showThermo "Left void: void + 3" $
    EVAdd mkVoid (mkPure 3)
  
  showThermo "Right void: 5 + void" $
    EVAdd (mkPure 5) mkVoid
  
  showThermo "Both void: void + void" $
    EVAdd mkVoid mkVoid
  
  putStrLn "Hypothesis: void + pure = entropy 1, void + void = entropy 4"
  putStrLn "Testing with multiplication...\n"
  
  showThermo "Left void: void * 3" $
    EVMul mkVoid (mkPure 3)
  
  showThermo "Both void: void * void" $
    EVMul mkVoid mkVoid
  
  putStrLn "--- EXPERIMENT 2: Entropy Layering ---"
  putStrLn "Does nesting change entropy composition?\n"
  
  showThermo "Flat: void + void + void" $
    EVAdd (EVAdd mkVoid mkVoid) mkVoid
  
  showThermo "Nested: (void + void) + (void + void)" $
    EVAdd (EVAdd mkVoid mkVoid) (EVAdd mkVoid mkVoid)
  
  showThermo "Deep nest: ((void + void) + void) + void" $
    EVAdd (EVAdd (EVAdd mkVoid mkVoid) mkVoid) mkVoid
  
  putStrLn "--- EXPERIMENT 3: Can We Contain Entropy? ---"
  putStrLn "Does default() affect the entropy ledger?\n"
  
  showThermo "Uncontained void" $
    mkVoid
  
  showThermo "Default-wrapped void: default(void, 42)" $
    EVDefault mkVoid (mkPure 42)
  
  showThermo "Default in chain: default(void, 10) + 5" $
    EVAdd (EVDefault mkVoid (mkPure 10)) (mkPure 5)
  
  showThermo "Multiple recoveries: default(void,1) + default(void,2)" $
    EVAdd (EVDefault mkVoid (mkPure 1)) (EVDefault mkVoid (mkPure 2))
  
  putStrLn "Question: Does recovery erase entropy or just stop propagation?"
  putStrLn ""
  
  putStrLn "--- EXPERIMENT 4: Entropy Derivatives ---"
  putStrLn "Marginal entropy: how much does each additional void cost?\n"
  
  let entropies = [
        ("0 voids", EVAdd (mkPure 1) (mkPure 2)),
        ("1 void", EVAdd mkVoid (mkPure 2)),
        ("2 voids", EVAdd mkVoid mkVoid),
        ("3 voids", EVAdd (EVAdd mkVoid mkVoid) mkVoid),
        ("4 voids", EVAdd (EVAdd mkVoid mkVoid) (EVAdd mkVoid mkVoid))
        ]
  
  mapM_ (\(label, expr) -> do
    let Pair _ u = run_thermo expr
    putStrLn $ label ++ ": entropy = " ++ show (total_entropy u)
    ) entropies
  
  putStrLn ""
  
  putStrLn "--- EXPERIMENT 5: Conditional Entropy ---"
  putStrLn "Does branching affect entropy differently?\n"
  
  showThermo "IfVoid with non-void condition: ifVoid(5, void, 42)" $
    EVIfVoid (mkPure 5) mkVoid (mkPure 42)
  
  showThermo "IfVoid with void condition: ifVoid(void, 10, 20)" $
    EVIfVoid mkVoid (mkPure 10) (mkPure 20)
  
  showThermo "Void in then branch (taken): ifVoid(void, void, 99)" $
    EVIfVoid mkVoid mkVoid (mkPure 99)
  
  showThermo "Void in else branch (not taken): ifVoid(void, 42, void)" $
    EVIfVoid mkVoid (mkPure 42) mkVoid
  
  putStrLn "--- EXPERIMENT 6: Entropy Shielding ---"
  putStrLn "Can we create void-containing structures?\n"
  
  showThermo "Let-binding a void (unused)" $
    EVLet "x" mkVoid (mkPure 42)
  
  showThermo "Let-binding a void (used)" $
    EVLet "x" mkVoid (EVAdd (EVVar "x") (mkPure 5))
  
  showThermo "Nested let with void" $
    EVLet "x" mkVoid $
      EVLet "y" (mkPure 10) $
        EVAdd (EVVar "y") (mkPure 5)
  
  putStrLn "Does defining but not using a void still incur entropy cost?"
  putStrLn ""
  
  putStrLn "--- EXPERIMENT 7: Entropy Amplification ---"
  putStrLn "Fibonacci-like void spreading:\n"
  
  let fib 0 = mkPure 1
      fib 1 = mkPure 1
      fib n = EVAdd (fib (n-1)) (fib (n-2))
  
  let voidFib 0 = mkVoid
      voidFib 1 = mkPure 1
      voidFib n = EVAdd (voidFib (n-1)) (voidFib (n-2))
  
  showThermo "Pure fibonacci(4)" $ fib 4
  showThermo "Void fibonacci(4) - void at base" $ voidFib 4
  
  putStrLn "--- FINAL EXPERIMENT: Entropy Conservation Test ---"
  putStrLn "Testing if (a+b)+c == a+(b+c) in entropy:\n"
  
  let left = EVAdd (EVAdd mkVoid (mkPure 5)) (mkPure 3)
  let right = EVAdd mkVoid (EVAdd (mkPure 5) (mkPure 3))
  
  let Pair _ u1 = run_thermo left
  let Pair _ u2 = run_thermo right
  
  putStrLn $ "Left-associative entropy: " ++ show (total_entropy u1)
  putStrLn $ "Right-associative entropy: " ++ show (total_entropy u2)
  
  if total_entropy u1 == total_entropy u2
    then putStrLn "✓ Associativity preserves entropy!"
    else putStrLn "✗ Entropy depends on evaluation order!"
  
  putStrLn "\n=== DISCOVERIES ==="
  putStrLn "? How does entropy compose?"
  putStrLn "? Does default() erase or contain entropy?"
  putStrLn "? Is there an entropy derivative (marginal cost)?"
  putStrLn "? Do unused voids contribute to entropy?"
  putStrLn "? Does evaluation order matter?"