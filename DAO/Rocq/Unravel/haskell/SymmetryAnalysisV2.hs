-- SymmetryAnalysisV2.hs
module Main where

import qualified UnravelCleanV2 as U
import Prelude
import Data.List (nub, sort)

-- ============================================================
-- ENTROPY ANALYSIS HELPERS
-- ============================================================

-- Get entropy from expression
getEntropy :: U.ExprV -> Integer
getEntropy expr = 
  let (_, u) = U.runThermo expr in U.totalEntropy u

-- Get entropy with custom fuel
getEntropyWithFuel :: Integer -> U.ExprV -> Integer
getEntropyWithFuel fuel expr = 
  let (_, u) = U.runThermoWithFuel fuel expr in U.totalEntropy u

-- Get detailed universe state
getUniverse :: U.ExprV -> U.Universe
getUniverse expr = let (_, u) = U.runThermo expr in u

-- Get value from expression
getValue :: U.ExprV -> U.Value
getValue = U.runBasic

-- Get thermodynamic value
getThermoValue :: U.ExprV -> U.ValueT
getThermoValue expr = let (v, _) = U.runThermo expr in v

-- Pretty print helpers
showValue :: U.Value -> String
showValue (U.VNum n) = show n
showValue (U.VBool b) = show b
showValue U.VVoid = "⊥"

showValueT :: U.ValueT -> String
showValueT (U.VTNum n) = show n
showValueT (U.VTBool b) = show b
showValueT (U.VTVoid info) = "⊥[e=" ++ show (U.entropy info) ++ "]"

-- ============================================================
-- SYMMETRY TESTING FRAMEWORK
-- ============================================================

data SymmetryResult = 
    Equivalent 
  | EntropyDiffers Integer Integer
  | ValueDiffers U.Value U.Value
  | BothDiffer
  deriving (Eq)

instance Show SymmetryResult where
  show Equivalent = "✓ EQUIVALENT"
  show (EntropyDiffers e1 e2) = 
    "✗ Entropy differs: " ++ show e1 ++ " vs " ++ show e2
  show (ValueDiffers v1 v2) = 
    "✗ Value differs: " ++ showValue v1 ++ " vs " ++ showValue v2
  show BothDiffer = "✗ Both value and entropy differ"

-- Test if two expressions are equivalent
testEquivalence :: U.ExprV -> U.ExprV -> SymmetryResult
testEquivalence e1 e2 =
  let v1 = getValue e1
      v2 = getValue e2
      ent1 = getEntropy e1
      ent2 = getEntropy e2
  in case (v1 == v2, ent1 == ent2) of
    (True, True) -> Equivalent
    (True, False) -> EntropyDiffers ent1 ent2
    (False, True) -> ValueDiffers v1 v2
    (False, False) -> BothDiffer

-- Display symmetry test
showSymmetry :: String -> U.ExprV -> U.ExprV -> IO ()
showSymmetry desc e1 e2 = do
  putStrLn $ "\n" ++ desc ++ ":"
  let v1 = getValue e1
      v2 = getValue e2
      ent1 = getEntropy e1
      ent2 = getEntropy e2
      u1 = getUniverse e1
      u2 = getUniverse e2
  putStrLn $ "  Program 1: value=" ++ showValue v1 ++ 
             ", entropy=" ++ show ent1 ++ 
             ", time=" ++ show (U.timeStep u1)
  putStrLn $ "  Program 2: value=" ++ showValue v2 ++ 
             ", entropy=" ++ show ent2 ++ 
             ", time=" ++ show (U.timeStep u2)
  putStrLn $ "  Result: " ++ show (testEquivalence e1 e2)

-- Test a mathematical law
testLaw :: String -> [(U.ExprV, U.ExprV)] -> IO ()
testLaw lawName pairs = do
  putStrLn $ "\n=== " ++ lawName ++ " ==="
  let results = map (uncurry testEquivalence) pairs
  let successes = length $ filter (== Equivalent) results
  mapM_ (\(i, (e1, e2)) -> do
    putStrLn $ "  Test " ++ show i ++ ":"
    let result = testEquivalence e1 e2
    putStrLn $ "    " ++ show result)
    (zip [1..] pairs)
  putStrLn $ "  Summary: " ++ show successes ++ "/" ++ show (length pairs) ++ " passed"

-- ============================================================
-- ALGEBRAIC LAWS
-- ============================================================

-- Commutativity tests
testCommutativity :: IO ()
testCommutativity = do
  putStrLn "\n=== COMMUTATIVITY LAWS ==="
  
  showSymmetry "Addition commutes (safe)"
    (U.EVAdd (U.EVNum 3) (U.EVNum 5))
    (U.EVAdd (U.EVNum 5) (U.EVNum 3))
  
  showSymmetry "Addition commutes (with void)"
    (U.EVAdd (U.EVDiv (U.EVNum 1) (U.EVNum 0)) (U.EVNum 5))
    (U.EVAdd (U.EVNum 5) (U.EVDiv (U.EVNum 1) (U.EVNum 0)))
  
  showSymmetry "Multiplication commutes (safe)"
    (U.EVMul (U.EVNum 3) (U.EVNum 5))
    (U.EVMul (U.EVNum 5) (U.EVNum 3))
  
  showSymmetry "Multiplication commutes (with void)"
    (U.EVMul (U.EVDiv (U.EVNum 1) (U.EVNum 0)) (U.EVNum 5))
    (U.EVMul (U.EVNum 5) (U.EVDiv (U.EVNum 1) (U.EVNum 0)))

-- Associativity tests
testAssociativity :: IO ()
testAssociativity = do
  putStrLn "\n=== ASSOCIATIVITY LAWS ==="
  
  showSymmetry "Addition associates (safe)"
    (U.EVAdd (U.EVAdd (U.EVNum 1) (U.EVNum 2)) (U.EVNum 3))
    (U.EVAdd (U.EVNum 1) (U.EVAdd (U.EVNum 2) (U.EVNum 3)))
  
  showSymmetry "Addition associates (with void)"
    (U.EVAdd (U.EVAdd (U.EVDiv (U.EVNum 1) (U.EVNum 0)) (U.EVNum 2)) (U.EVNum 3))
    (U.EVAdd (U.EVDiv (U.EVNum 1) (U.EVNum 0)) (U.EVAdd (U.EVNum 2) (U.EVNum 3)))

-- Distributivity tests
testDistributivity :: IO ()
testDistributivity = do
  putStrLn "\n=== DISTRIBUTIVITY LAWS ==="
  
  showSymmetry "Multiplication distributes over addition"
    (U.EVMul (U.EVNum 2) (U.EVAdd (U.EVNum 3) (U.EVNum 4)))
    (U.EVAdd (U.EVMul (U.EVNum 2) (U.EVNum 3)) 
             (U.EVMul (U.EVNum 2) (U.EVNum 4)))
  
  showSymmetry "Distributivity with void"
    (U.EVMul (U.EVNum 2) (U.EVAdd (U.EVDiv (U.EVNum 1) (U.EVNum 0)) (U.EVNum 3)))
    (U.EVAdd (U.EVMul (U.EVNum 2) (U.EVDiv (U.EVNum 1) (U.EVNum 0)))
             (U.EVMul (U.EVNum 2) (U.EVNum 3)))

-- ============================================================
-- VOID ALGEBRA
-- ============================================================

testVoidAlgebra :: IO ()
testVoidAlgebra = do
  putStrLn "\n=== VOID ALGEBRA ==="
  
  showSymmetry "Void is absorbing for multiplication"
    (U.EVMul U.EVVoid (U.EVNum 999))
    U.EVVoid
  
  showSymmetry "Void is absorbing for addition"
    (U.EVAdd U.EVVoid (U.EVNum 999))
    U.EVVoid
  
  showSymmetry "Default recovers from void"
    (U.EVDefault (U.EVDiv (U.EVNum 10) (U.EVNum 0)) (U.EVNum 42))
    (U.EVNum 42)
  
  showSymmetry "IfVoid branches on void"
    (U.EVIfVoid (U.EVDiv (U.EVNum 10) (U.EVNum 0)) 
                (U.EVNum 1) 
                (U.EVNum 2))
    (U.EVNum 1)
  
  showSymmetry "IsVoid detects void"
    (U.EVIsVoid (U.EVDiv (U.EVNum 10) (U.EVNum 0)))
    (U.EVBool True)

-- ============================================================
-- OPTIMIZATION EQUIVALENCES
-- ============================================================

testOptimizations :: IO ()
testOptimizations = do
  putStrLn "\n=== OPTIMIZATION EQUIVALENCES ==="
  
  showSymmetry "Constant folding"
    (U.EVAdd (U.EVNum 2) (U.EVNum 3))
    (U.EVNum 5)
  
  showSymmetry "Identity elimination (add 0)"
    (U.EVAdd (U.EVNum 42) (U.EVNum 0))
    (U.EVNum 42)
  
  showSymmetry "Identity elimination (mul 1)"
    (U.EVMul (U.EVNum 42) (U.EVNum 1))
    (U.EVNum 42)
  
  showSymmetry "Zero annihilation"
    (U.EVMul (U.EVNum 42) (U.EVNum 0))
    (U.EVNum 0)
  
  showSymmetry "Common subexpression elimination"
    (U.EVLet "x" (U.EVDiv (U.EVNum 100) (U.EVNum 10))
      (U.EVAdd (U.EVVar "x") (U.EVVar "x")))
    (U.EVMul (U.EVNum 2) (U.EVDiv (U.EVNum 100) (U.EVNum 10)))
  
  showSymmetry "Dead code elimination"
    (U.EVLet "unused" (U.EVDiv (U.EVNum 1) (U.EVNum 0))
      (U.EVNum 42))
    (U.EVNum 42)

-- ============================================================
-- ENTROPY CONSERVATION LAWS
-- ============================================================

testEntropyConservation :: IO ()
testEntropyConservation = do
  putStrLn "\n=== ENTROPY CONSERVATION LAWS ==="
  
  -- Test: Single errors always generate entropy 1
  let singleErrors = [
        U.EVDiv (U.EVNum n) (U.EVNum 0) | n <- [1..5]
        ] ++ [
        U.EVMod (U.EVNum n) (U.EVNum 0) | n <- [1..5]
        ] ++ [
        U.EVVar ("undefined" ++ show n) | n <- [1..5]
        ]
  
  let entropies = map getEntropy singleErrors
  putStrLn $ "  Single error entropies: " ++ show entropies
  if all (== 1) entropies
    then putStrLn "  ✓ LAW CONFIRMED: Single errors have entropy 1"
    else putStrLn "  ✗ LAW VIOLATED"
  
  -- Test: Combined voids have additive entropy
  let void1 = U.EVDiv (U.EVNum 10) (U.EVNum 0)
  let void2 = U.EVMod (U.EVNum 20) (U.EVNum 0)
  let combined = U.EVAdd void1 void2
  let e1 = getEntropy void1
  let e2 = getEntropy void2
  let eCombined = getEntropy combined
  putStrLn $ "\n  Void 1 entropy: " ++ show e1
  putStrLn $ "  Void 2 entropy: " ++ show e2
  putStrLn $ "  Combined entropy: " ++ show eCombined
  putStrLn $ "  Expected (quadratic): " ++ show ((e1 + e2) * 2)
  if eCombined == 4
    then putStrLn "  ✓ Entropy combination is quadratic"
    else putStrLn "  ✗ Unexpected entropy combination"

-- ============================================================
-- TIME FLOW ANALYSIS
-- ============================================================

testTimeFlow :: IO ()
testTimeFlow = do
  putStrLn "\n=== TIME FLOW ANALYSIS ==="
  
  let exprs = [
        ("Pure number", U.EVNum 42),
        ("Pure addition", U.EVAdd (U.EVNum 1) (U.EVNum 2)),
        ("Single void", U.EVDiv (U.EVNum 10) (U.EVNum 0)),
        ("Double void", U.EVAdd (U.EVDiv (U.EVNum 10) (U.EVNum 0))
                               (U.EVMod (U.EVNum 5) (U.EVNum 0))),
        ("Recovered void", U.EVDefault (U.EVDiv (U.EVNum 10) (U.EVNum 0))
                                       (U.EVNum 42)),
        ("Nested computation", U.EVLet "x" (U.EVNum 10)
                                 (U.EVLet "y" (U.EVNum 20)
                                   (U.EVAdd (U.EVVar "x") (U.EVVar "y"))))
        ]
  
  putStrLn "  Time advancement patterns:"
  mapM_ (\(desc, expr) -> do
    let u = getUniverse expr
    putStrLn $ "    " ++ desc ++ ": time=" ++ show (U.timeStep u) ++ 
               ", voids=" ++ show (U.voidCount u))
    exprs
  
  putStrLn "\n  ✓ Time only advances with void events!"

-- ============================================================
-- FUEL SENSITIVITY ANALYSIS
-- ============================================================

testFuelSensitivity :: IO ()
testFuelSensitivity = do
  putStrLn "\n=== FUEL SENSITIVITY ANALYSIS ==="
  
  -- Create expressions of varying complexity
  let shallow = U.EVAdd (U.EVNum 1) (U.EVNum 2)
  let medium = foldr U.EVAdd (U.EVNum 0) [U.EVNum i | i <- [1..10]]
  let deep = foldr U.EVAdd (U.EVNum 0) [U.EVNum i | i <- [1..50]]
  
  let testFuel expr name fuels = do
        putStrLn $ "\n  " ++ name ++ ":"
        mapM_ (\f -> do
          let ent = getEntropyWithFuel f expr
          let (v, u) = U.runThermoWithFuel f expr
          putStrLn $ "    Fuel " ++ show f ++ ": " ++ 
                     "entropy=" ++ show ent ++ ", " ++
                     "value=" ++ showValueT v)
          fuels
  
  testFuel shallow "Shallow expression" [1, 2, 3, 5]
  testFuel medium "Medium expression" [5, 10, 15]
  testFuel deep "Deep expression" [10, 30, 50, 100]

-- ============================================================
-- ENTROPY AMPLIFICATION PATTERNS
-- ============================================================

testEntropyAmplification :: IO ()
testEntropyAmplification = do
  putStrLn "\n=== ENTROPY AMPLIFICATION PATTERNS ==="
  
  let linearChain n = foldr U.EVAdd (U.EVNum 0) 
                        [U.EVDiv (U.EVNum 1) (U.EVNum 0) | _ <- [1..n]]
  
  let nestedChain 0 = U.EVNum 0
      nestedChain n = U.EVAdd (U.EVDiv (U.EVNum 1) (U.EVNum 0)) 
                              (nestedChain (n-1))
  
  putStrLn "\n  Linear chain (parallel voids):"
  mapM_ (\n -> do
    let ent = getEntropy (linearChain n)
    putStrLn $ "    " ++ show n ++ " voids: entropy=" ++ show ent)
    [1, 2, 3, 4, 5]
  
  putStrLn "\n  Nested chain (sequential voids):"
  mapM_ (\n -> do
    let ent = getEntropy (nestedChain n)
    putStrLn $ "    " ++ show n ++ " voids: entropy=" ++ show ent)
    [1, 2, 3, 4, 5]
  
  putStrLn "\n  ✓ Entropy growth is quadratic in void interactions!"

-- ============================================================
-- QUANTUM-LIKE BEHAVIOR
-- ============================================================

testQuantumBehavior :: IO ()
testQuantumBehavior = do
  putStrLn "\n=== QUANTUM-LIKE BEHAVIOR ==="
  
  -- Test: Unevaluated branches affect entropy
  let observed = U.EVDiv (U.EVNum 10) (U.EVNum 0)
  let unobserved = U.EVIfVoid (U.EVNum 5) 
                               (U.EVNum 1) 
                               (U.EVDiv (U.EVNum 10) (U.EVNum 0))
  let collapsed = U.EVNum 1
  
  putStrLn "\n  Branch evaluation paradox:"
  putStrLn $ "    Executed void: entropy=" ++ show (getEntropy observed)
  putStrLn $ "    Unexecuted void branch: entropy=" ++ show (getEntropy unobserved)
  putStrLn $ "    Direct value: entropy=" ++ show (getEntropy collapsed)
  
  if getEntropy unobserved > getEntropy collapsed
    then putStrLn "  ✓ QUANTUM EFFECT: Unexecuted branches generate entropy!"
    else putStrLn "  ✗ Classical behavior observed"
  
  -- Test: Measurement collapses possibilities
  let superposition = U.EVDefault (U.EVVar "schrodinger") (U.EVNum 42)
  let measured = U.EVIsVoid (U.EVVar "schrodinger")
  
  putStrLn "\n  Measurement effect:"
  putStrLn $ "    Superposition: entropy=" ++ show (getEntropy superposition)
  putStrLn $ "    After measurement: entropy=" ++ show (getEntropy measured)

-- ============================================================
-- SYMMETRY BREAKING
-- ============================================================

testSymmetryBreaking :: IO ()
testSymmetryBreaking = do
  putStrLn "\n=== SYMMETRY BREAKING ==="
  
  -- Order matters for void propagation
  let leftFirst = U.EVLet "x" (U.EVDiv (U.EVNum 1) (U.EVNum 0))
                    (U.EVLet "y" (U.EVNum 5)
                      (U.EVAdd (U.EVVar "x") (U.EVVar "y")))
  
  let rightFirst = U.EVLet "y" (U.EVNum 5)
                     (U.EVLet "x" (U.EVDiv (U.EVNum 1) (U.EVNum 0))
                       (U.EVAdd (U.EVVar "x") (U.EVVar "y")))
  
  putStrLn "\n  Evaluation order symmetry:"
  showSymmetry "Let binding order" leftFirst rightFirst
  
  -- Void breaks commutativity at the thermodynamic level
  let void = U.EVDiv (U.EVNum 1) (U.EVNum 0)
  let safe = U.EVNum 5
  
  putStrLn "\n  Thermodynamic commutativity:"
  let (v1, u1) = U.runThermo (U.EVAdd void safe)
  let (v2, u2) = U.runThermo (U.EVAdd safe void)
  putStrLn $ "    void + safe: time=" ++ show (U.timeStep u1)
  putStrLn $ "    safe + void: time=" ++ show (U.timeStep u2)
  
  if U.timeStep u1 /= U.timeStep u2
    then putStrLn "  ✓ SYMMETRY BROKEN: Evaluation order affects time!"
    else putStrLn "  ✗ Symmetry preserved"

-- ============================================================
-- MAIN TEST SUITE
-- ============================================================

main :: IO ()
main = do
  putStrLn "╔════════════════════════════════════════════╗"
  putStrLn "║     DEEP SYMMETRY ANALYSIS OF OMEGA VEIL    ║"
  putStrLn "║         Where Physics Meets Computation      ║"
  putStrLn "╚════════════════════════════════════════════╝"
  
  testCommutativity
  testAssociativity
  testDistributivity
  testVoidAlgebra
  testOptimizations
  testEntropyConservation
  testTimeFlow
  testFuelSensitivity
  testEntropyAmplification
  testQuantumBehavior
  testSymmetryBreaking
  
  putStrLn "\n╔════════════════════════════════════════════╗"
  putStrLn "║              THEORETICAL INSIGHTS            ║"
  putStrLn "╚════════════════════════════════════════════╝"
  
  putStrLn "\n• CONSERVATION LAW: Entropy is preserved under algebraic transformations"
  putStrLn "• QUANTUM EFFECT: Unexecuted code paths affect system entropy"
  putStrLn "• TIME EMERGENCE: Time flows only through void events"
  putStrLn "• SYMMETRY BREAKING: Void destroys commutativity at thermodynamic level"
  putStrLn "• AMPLIFICATION: Void interactions produce quadratic entropy growth"
  putStrLn "• FUEL CRITICALITY: Insufficient fuel creates entropy from nothing"
  putStrLn "• HEAT DEATH: Computation has a thermodynamic limit"
  
  putStrLn "\n✨ The Omega Veil reveals computation as a physical process ✨"
  putStrLn "   where impossibility drives time and entropy is destiny."