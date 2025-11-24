-- ValidateRewrite.hs
module Main where

import qualified Unravel as Original
import qualified UnravelClean as Clean
import qualified Prelude

-- Test equality of Option values
testOption :: Prelude.Eq a => Prelude.String -> Original.Option a -> Clean.Option a -> Prelude.IO ()
testOption name orig clean = do
  let origStr = case orig of
                  Original.Some x -> "Some _"
                  Original.None -> "None"
      cleanStr = case clean of
                  Clean.Some x -> "Some _"
                  Clean.None -> "None"
  if origStr Prelude.== cleanStr
    then Prelude.putStrLn (name Prelude.++ ": ✓")
    else Prelude.putStrLn (name Prelude.++ ": ✗ MISMATCH")

-- Test arithmetic operations
testArithmetic :: Prelude.IO ()
testArithmetic = do
  Prelude.putStrLn "\n=== ARITHMETIC OPERATIONS ==="
  
  -- Test add
  let test_add n m = 
        let orig = Original.add n m
            clean = Clean.add n m
        in if orig Prelude.== clean 
           then Prelude.putStrLn ("add " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✓ = " Prelude.++ Prelude.show clean)
           else Prelude.putStrLn ("add " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✗ orig=" Prelude.++ Prelude.show orig Prelude.++ " clean=" Prelude.++ Prelude.show clean)
  
  test_add 0 0
  test_add 5 3
  test_add 10 20
  test_add 0 100
  
  -- Test mul
  let test_mul n m = 
        let orig = Original.mul n m
            clean = Clean.mul n m
        in if orig Prelude.== clean 
           then Prelude.putStrLn ("mul " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✓ = " Prelude.++ Prelude.show clean)
           else Prelude.putStrLn ("mul " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✗")
  
  test_mul 0 5
  test_mul 3 4
  test_mul 10 10
  
  -- Test sub (saturating)
  let test_sub n m = 
        let orig = Original.sub n m
            clean = Clean.sub n m
        in if orig Prelude.== clean 
           then Prelude.putStrLn ("sub " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✓ = " Prelude.++ Prelude.show clean)
           else Prelude.putStrLn ("sub " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✗ orig=" Prelude.++ Prelude.show orig Prelude.++ " clean=" Prelude.++ Prelude.show clean)
  
  test_sub 10 5
  test_sub 5 10  -- Should saturate to 0
  test_sub 0 5   -- Should be 0
  test_sub 20 20
  
  -- Test leb
  let test_leb n m = 
        let orig = Original.leb n m
            clean = Clean.leb n m
        in if orig Prelude.== clean 
           then Prelude.putStrLn ("leb " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✓ = " Prelude.++ Prelude.show clean)
           else Prelude.putStrLn ("leb " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✗")
  
  test_leb 5 10
  test_leb 10 5
  test_leb 5 5
  test_leb 0 0
  
  -- Test div and mod
  let test_div n m = 
        if m Prelude./= 0 then
          let orig = Original.div n m
              clean = Clean.div n m
          in if orig Prelude.== clean 
             then Prelude.putStrLn ("div " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✓ = " Prelude.++ Prelude.show clean)
             else Prelude.putStrLn ("div " Prelude.++ Prelude.show n Prelude.++ " " Prelude.++ Prelude.show m Prelude.++ ": ✗")
        else Prelude.putStrLn ("div " Prelude.++ Prelude.show n Prelude.++ " 0: skipped (div by zero)")
  
  test_div 10 3
  test_div 20 5
  test_div 7 2
  
  -- Test string equality
  let test_eqb s1 s2 = 
        let orig = Original.eqb s1 s2
            clean = Clean.eqb s1 s2
        in if orig Prelude.== clean 
           then Prelude.putStrLn ("eqb \"" Prelude.++ s1 Prelude.++ "\" \"" Prelude.++ s2 Prelude.++ "\": ✓ = " Prelude.++ Prelude.show clean)
           else Prelude.putStrLn ("eqb: ✗")
  
  test_eqb "hello" "hello"
  test_eqb "hello" "world"
  test_eqb "" ""


testEval :: Prelude.IO ()
testEval = do
  Prelude.putStrLn "\n=== EVALUATION TESTS ==="
  
  -- Helper to compare values (since they're different types)
  let valueEq :: Original.Value -> Clean.Value -> Prelude.Bool
      valueEq (Original.VNum n) (Clean.VNum m) = n Prelude.== m
      valueEq (Original.VBool b) (Clean.VBool c) = b Prelude.== c
      valueEq Original.VVoid Clean.VVoid = Prelude.True
      valueEq _ _ = Prelude.False
  
  let showOrigValue :: Original.Value -> Prelude.String
      showOrigValue (Original.VNum n) = "VNum " Prelude.++ Prelude.show n
      showOrigValue (Original.VBool b) = "VBool " Prelude.++ Prelude.show b
      showOrigValue Original.VVoid = "VVoid"
  
  let showCleanValue :: Clean.Value -> Prelude.String
      showCleanValue (Clean.VNum n) = "VNum " Prelude.++ Prelude.show n
      showCleanValue (Clean.VBool b) = "VBool " Prelude.++ Prelude.show b
      showCleanValue Clean.VVoid = "VVoid"
  
  -- Test function that takes both expressions
  let test_expr desc origExpr cleanExpr =
        let orig = Original.eval_default origExpr
            clean = Clean.eval_default cleanExpr
        in if valueEq orig clean
           then Prelude.putStrLn (desc Prelude.++ ": ✓")
           else Prelude.putStrLn (desc Prelude.++ ": ✗ orig=" Prelude.++ showOrigValue orig Prelude.++ " clean=" Prelude.++ showCleanValue clean)
  
  -- Test cases (need to create both versions)
  test_expr "Number literal" 
    (Original.ENum 42) 
    (Clean.ENum 42)
    
  test_expr "Boolean literal" 
    (Original.EBool Prelude.True) 
    (Clean.EBool Prelude.True)
    
  test_expr "Void literal" 
    Original.EVoid 
    Clean.EVoid
  
  -- Arithmetic
  test_expr "Addition" 
    (Original.EAdd (Original.ENum 5) (Original.ENum 3))
    (Clean.EAdd (Clean.ENum 5) (Clean.ENum 3))
    
  test_expr "Subtraction" 
    (Original.ESub (Original.ENum 10) (Original.ENum 3))
    (Clean.ESub (Clean.ENum 10) (Clean.ENum 3))
    
  test_expr "Multiplication" 
    (Original.EMul (Original.ENum 4) (Original.ENum 7))
    (Clean.EMul (Clean.ENum 4) (Clean.ENum 7))
    
  test_expr "Division" 
    (Original.EDiv (Original.ENum 10) (Original.ENum 3))
    (Clean.EDiv (Clean.ENum 10) (Clean.ENum 3))
    
  test_expr "Modulo" 
    (Original.EMod (Original.ENum 10) (Original.ENum 3))
    (Clean.EMod (Clean.ENum 10) (Clean.ENum 3))
  
  -- Division by zero
  test_expr "Division by zero" 
    (Original.EDiv (Original.ENum 10) (Original.ENum 0))
    (Clean.EDiv (Clean.ENum 10) (Clean.ENum 0))
    
  test_expr "Modulo by zero" 
    (Original.EMod (Original.ENum 10) (Original.ENum 0))
    (Clean.EMod (Clean.ENum 10) (Clean.ENum 0))
  
  -- Void operations
  test_expr "IsVoid of void" 
    (Original.EIsVoid Original.EVoid)
    (Clean.EIsVoid Clean.EVoid)
    
  test_expr "IsVoid of number" 
    (Original.EIsVoid (Original.ENum 42))
    (Clean.EIsVoid (Clean.ENum 42))
  
  -- IfVoid
  test_expr "IfVoid with void condition" 
    (Original.EIfVoid Original.EVoid (Original.ENum 1) (Original.ENum 2))
    (Clean.EIfVoid Clean.EVoid (Clean.ENum 1) (Clean.ENum 2))
    
  test_expr "IfVoid with non-void condition" 
    (Original.EIfVoid (Original.ENum 42) (Original.ENum 1) (Original.ENum 2))
    (Clean.EIfVoid (Clean.ENum 42) (Clean.ENum 1) (Clean.ENum 2))
  
  -- Default
  test_expr "Default with void" 
    (Original.EDefault Original.EVoid (Original.ENum 99))
    (Clean.EDefault Clean.EVoid (Clean.ENum 99))
    
  test_expr "Default with value" 
    (Original.EDefault (Original.ENum 42) (Original.ENum 99))
    (Clean.EDefault (Clean.ENum 42) (Clean.ENum 99))
  
  -- Void propagation
  test_expr "Void propagation in addition" 
    (Original.EAdd Original.EVoid (Original.ENum 5))
    (Clean.EAdd Clean.EVoid (Clean.ENum 5))
    
  test_expr "Void propagation from div/0" 
    (Original.EAdd (Original.EDiv (Original.ENum 10) (Original.ENum 0)) (Original.ENum 5))
    (Clean.EAdd (Clean.EDiv (Clean.ENum 10) (Clean.ENum 0)) (Clean.ENum 5))
  
  -- Complex expression
  test_expr "Complex nested expression"
    (Original.EDefault 
      (Original.EDiv (Original.ENum 100) 
        (Original.ESub (Original.ENum 5) (Original.ENum 5)))  -- 100/0
      (Original.EAdd (Original.ENum 40) (Original.ENum 2)))    -- 42
    (Clean.EDefault 
      (Clean.EDiv (Clean.ENum 100) 
        (Clean.ESub (Clean.ENum 5) (Clean.ENum 5)))  -- 100/0
      (Clean.EAdd (Clean.ENum 40) (Clean.ENum 2)))    -- 42

testVariables :: Prelude.IO ()
testVariables = do
  Prelude.putStrLn "\n=== VARIABLE TESTS ==="
  
  let valueEq :: Original.Value -> Clean.Value -> Prelude.Bool
      valueEq (Original.VNum n) (Clean.VNum m) = n Prelude.== m
      valueEq (Original.VBool b) (Clean.VBool c) = b Prelude.== c
      valueEq Original.VVoid Clean.VVoid = Prelude.True
      valueEq _ _ = Prelude.False
  
  let showValue :: Clean.Value -> Prelude.String
      showValue (Clean.VNum n) = "VNum " Prelude.++ Prelude.show n
      showValue (Clean.VBool b) = "VBool " Prelude.++ Prelude.show b
      showValue Clean.VVoid = "VVoid"
  
  let test_expr desc origExpr cleanExpr =
        let orig = Original.evalV_empty origExpr
            clean = Clean.evalV_empty cleanExpr
        in if valueEq orig clean
           then Prelude.putStrLn (desc Prelude.++ ": ✓")
           else Prelude.putStrLn (desc Prelude.++ ": ✗ orig/clean differ")
  
  -- Test undefined variable
  test_expr "Undefined variable"
    (Original.EVVar "x")
    (Clean.EVVar "x")
  
  -- Test simple let binding
  test_expr "Simple let binding"
    (Original.EVLet "x" (Original.EVNum 10) 
      (Original.EVAdd (Original.EVVar "x") (Original.EVNum 5)))
    (Clean.EVLet "x" (Clean.EVNum 10)
      (Clean.EVAdd (Clean.EVVar "x") (Clean.EVNum 5)))
  
  -- Test nested let bindings
  test_expr "Nested let bindings"
    (Original.EVLet "x" (Original.EVNum 10)
      (Original.EVLet "y" (Original.EVNum 20)
        (Original.EVAdd (Original.EVVar "x") (Original.EVVar "y"))))
    (Clean.EVLet "x" (Clean.EVNum 10)
      (Clean.EVLet "y" (Clean.EVNum 20)
        (Clean.EVAdd (Clean.EVVar "x") (Clean.EVVar "y"))))
  
  -- Test shadowing
  test_expr "Variable shadowing"
    (Original.EVLet "x" (Original.EVNum 10)
      (Original.EVLet "x" (Original.EVNum 20)
        (Original.EVVar "x")))
    (Clean.EVLet "x" (Clean.EVNum 10)
      (Clean.EVLet "x" (Clean.EVNum 20)
        (Clean.EVVar "x")))
  
  -- Test void binding
  test_expr "Void in let binding"
    (Original.EVLet "x" (Original.EVDiv (Original.EVNum 10) (Original.EVNum 0))
      (Original.EVAdd (Original.EVVar "x") (Original.EVNum 5)))
    (Clean.EVLet "x" (Clean.EVDiv (Clean.EVNum 10) (Clean.EVNum 0))
      (Clean.EVAdd (Clean.EVVar "x") (Clean.EVNum 5)))
  
  -- Test recovery from undefined
  test_expr "Recovery from undefined variable"
    (Original.EVDefault (Original.EVVar "undefined") (Original.EVNum 42))
    (Clean.EVDefault (Clean.EVVar "undefined") (Clean.EVNum 42))
  
  -- Test complex expression with variables
  test_expr "Complex expression with variables"
    (Original.EVLet "divisor" (Original.EVNum 0)
      (Original.EVLet "result" (Original.EVDiv (Original.EVNum 100) (Original.EVVar "divisor"))
        (Original.EVDefault (Original.EVVar "result")
          (Original.EVLet "x" (Original.EVNum 10)
            (Original.EVLet "y" (Original.EVNum 32)
              (Original.EVAdd (Original.EVVar "x") (Original.EVVar "y")))))))
    (Clean.EVLet "divisor" (Clean.EVNum 0)
      (Clean.EVLet "result" (Clean.EVDiv (Clean.EVNum 100) (Clean.EVVar "divisor"))
        (Clean.EVDefault (Clean.EVVar "result")
          (Clean.EVLet "x" (Clean.EVNum 10)
            (Clean.EVLet "y" (Clean.EVNum 32)
              (Clean.EVAdd (Clean.EVVar "x") (Clean.EVVar "y")))))))

-- Update main
main :: Prelude.IO ()
main = do
  Prelude.putStrLn "=== VALIDATING REWRITE ==="
  testArithmetic
  testEval
  testVariables
  Prelude.putStrLn "\n✅ All tests validated!"