-- VoidLangWrapper.hs
import VoidLang

-- Helper to convert normal Integers
fromInt :: Integer -> Expr
fromInt n = ENum n

-- Pretty printer
showValue :: Value -> String
showValue (VNum n) = show n
showValue (VBool True) = "true"
showValue (VBool False) = "false"
showValue VVoid = "∅ (void)"

-- Better eval with reasonable fuel
evalExpr :: Expr -> Value
evalExpr = eval 100  -- 100 is enough!

-- Demo function
demo :: String -> Expr -> IO ()
demo desc expr = do
  let result = evalExpr expr
  putStrLn $ desc ++ " = " ++ showValue result

main :: IO ()
main = do
  putStrLn "=== Welcome to VoidLang ==="
  putStrLn "Where Nothing Is Something!\n"
  
  putStrLn "--- Basic Arithmetic ---"
  demo "5 + 3" $ EAdd (fromInt 5) (fromInt 3)
  demo "10 - 4" $ ESub (fromInt 10) (fromInt 4)
  demo "6 * 7" $ EMul (fromInt 6) (fromInt 7)
  demo "20 / 4" $ EDiv (fromInt 20) (fromInt 4)
  
  putStrLn "\n--- Void Behavior ---"
  demo "10 / 0" $ EDiv (fromInt 10) (fromInt 0)
  demo "5 + (10 / 0)" $ EAdd (fromInt 5) (EDiv (fromInt 10) (fromInt 0))
  demo "void + 42" $ EAdd EVoid (fromInt 42)
  
  putStrLn "\n--- Void Detection ---"
  demo "isVoid(10 / 0)" $ EIsVoid (EDiv (fromInt 10) (fromInt 0))
  demo "isVoid(10 / 2)" $ EIsVoid (EDiv (fromInt 10) (fromInt 2))
  
  putStrLn "\n--- Recovery from Void ---"
  demo "default(10/0, 999)" $ EDefault (EDiv (fromInt 10) (fromInt 0)) (fromInt 999)
  demo "default(10/2, 999)" $ EDefault (EDiv (fromInt 10) (fromInt 2)) (fromInt 999)
  
  putStrLn "\n--- Conditional on Void ---"
  demo "if void(10/0) then 1 else 2" $ 
    EIfVoid (EDiv (fromInt 10) (fromInt 0)) (fromInt 1) (fromInt 2)
  demo "if void(10/2) then 1 else 2" $ 
    EIfVoid (EDiv (fromInt 10) (fromInt 2)) (fromInt 1) (fromInt 2)
  
  putStrLn "\n--- Complex Expression ---"
  let complex = EDefault 
        (EAdd (EDiv (fromInt 100) (fromInt 0)) 
              (EMul (fromInt 5) (fromInt 3)))
        (EAdd (fromInt 42) (fromInt 58))
  demo "(100/0 + 5*3) default (42+58)" complex
  
  putStrLn "\n--- The Philosophy ---"
  putStrLn "In VoidLang, errors don't crash - they flow."
  putStrLn "The void (∅) is not absence but presence."
  putStrLn "Every impossible operation returns to the source: omega_veil."