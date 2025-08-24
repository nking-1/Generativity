-- UnravelV2StressTest.hs
-- Comprehensive stress testing of the clean V2 Unravel reference
-- Designed to match our TypeScript diabolical testing patterns

import UnravelCleanV2
import Control.Monad (when)

-- ============================================================================
-- ENTROPY BOMB TEST (Key Diagnostic)
-- ============================================================================

-- Create entropy bomb using V2 spec
entropyBombV2 :: Integer -> ExprV
entropyBombV2 0 = EVDiv (EVNum 1) (EVNum 0)
entropyBombV2 n = EVAdd (entropyBombV2 (n-1)) (entropyBombV2 (n-1))

testEntropyBombV2 :: IO ()
testEntropyBombV2 = do
  putStrLn "💥 V2 ENTROPY BOMB TEST"
  putStrLn "Testing the exact pattern that revealed TypeScript fuel issues...\n"
  
  putStrLn "V2 Entropy bomb progression:"
  mapM_ (\depth -> do
    let expr = entropyBombV2 depth
    let (v, u) = runThermo expr
    putStrLn $ "  V2 Bomb " ++ show depth ++ 
               ": entropy=" ++ show (totalEntropy u) ++ 
               ", time=" ++ show (timeStep u) ++ 
               ", voids=" ++ show (voidCount u)
    
    -- Check for consistency: time should equal voids in most cases
    when (timeStep u /= voidCount u && depth > 0) $
      putStrLn $ "    🤔 TIME/VOID MISMATCH: time=" ++ show (timeStep u) ++ 
                 ", voids=" ++ show (voidCount u)
    
    -- Check for heat death
    when (isHeatDeath u) $
      putStrLn $ "    🔥 HEAT DEATH REACHED at entropy=" ++ show (totalEntropy u)
    ) [0..12]

-- ============================================================================
-- MATHEMATICAL LAW VERIFICATION (V2)
-- ============================================================================

testMathLawsV2 :: IO ()
testMathLawsV2 = do
  putStrLn "\n🧮 V2 MATHEMATICAL LAW VERIFICATION"
  putStrLn "Testing Noether's theorem and conservation laws...\n"
  
  -- Test Noether's theorem (commutativity)
  let noetherTestsV2 = [(a, b) | a <- [1..200], b <- [1..50]]  -- Extensive testing
  let noetherResults = map (\(a, b) ->
        let expr1 = EVAdd (EVNum a) (EVNum b)
            expr2 = EVAdd (EVNum b) (EVNum a)
            entropy1 = case runThermo expr1 of (_, u) -> totalEntropy u
            entropy2 = case runThermo expr2 of (_, u) -> totalEntropy u
        in entropy1 == entropy2) noetherTestsV2
  
  let noetherViolations = length (filter not noetherResults)
  let noetherTotal = length noetherResults
  
  putStrLn $ "Noether's theorem (V2): " ++ show noetherViolations ++ "/" ++ 
             show noetherTotal ++ " violations"
  putStrLn $ "V2 Success rate: " ++ 
             show (fromIntegral (noetherTotal - noetherViolations) / fromIntegral noetherTotal * 100) ++ "%"
  
  -- Test conservation laws
  putStrLn "\nTesting conservation laws (V2):"
  let conservationTestsV2 = [1..2000]  -- Extensive conservation testing
  let conservationResults = map (\n ->
        let voidExpr = EVDiv (EVNum n) (EVNum 0)
            recoveredExpr = EVDefault voidExpr (EVNum 999)
            voidEntropy = case runThermo voidExpr of (_, u) -> totalEntropy u
            recoveredEntropy = case runThermo recoveredExpr of (_, u) -> totalEntropy u
        in voidEntropy == recoveredEntropy) conservationTestsV2
  
  let conservationViolations = length (filter not conservationResults)
  let conservationTotal = length conservationResults
  
  putStrLn $ "Conservation laws (V2): " ++ show conservationViolations ++ "/" ++ 
             show conservationTotal ++ " violations"
  putStrLn $ "V2 Conservation rate: " ++ 
             show (fromIntegral (conservationTotal - conservationViolations) / fromIntegral conservationTotal * 100) ++ "%"

-- ============================================================================
-- FUEL MECHANISM ANALYSIS (V2)
-- ============================================================================

testFuelMechanismV2 :: IO ()
testFuelMechanismV2 = do
  putStrLn "\n⛽ V2 FUEL MECHANISM ANALYSIS"
  putStrLn "Testing fuel consumption patterns and limits...\n"
  
  -- Test with different fuel amounts
  let complexExpr = foldl1 EVAdd [EVDiv (EVNum n) (EVNum 0) | n <- [1..50]]
  let fuelAmounts = [100, 500, 1000, 2000, 5000, 10000]
  
  putStrLn "V2 Fuel consumption analysis:"
  mapM_ (\fuel -> do
    let (v, u) = evalTWithFuel fuel complexExpr
    let resultType = case v of
          VTNum _ -> "SUCCESS"
          VTVoid (VInfo _ _ OutOfFuel) -> "FUEL_EXHAUSTED"
          VTVoid _ -> "VOID"
          _ -> "OTHER"
    
    putStrLn $ "  Fuel " ++ show fuel ++ ": " ++ resultType ++ 
               " (entropy=" ++ show (totalEntropy u) ++ 
               ", time=" ++ show (timeStep u) ++ ")"
    ) fuelAmounts
  
  -- Test fuel efficiency vs expression complexity
  putStrLn "\nV2 Fuel efficiency analysis:"
  mapM_ (\complexity -> do
    let expr = entropyBombV2 complexity
    let (v, u) = runThermoWithFuel 10000 expr  -- High fuel
    let fuelUsed = 10000 - (case evalTWithFuel 10000 (EVNum 1) of (_, u') -> 10000)  -- Rough estimate
    
    putStrLn $ "  Complexity " ++ show complexity ++ 
               ": entropy=" ++ show (totalEntropy u) ++ 
               ", voids=" ++ show (voidCount u) ++ 
               ", time=" ++ show (timeStep u)
    ) [0..8]

-- ============================================================================
-- VARIABLE ENVIRONMENT TESTING (V2)
-- ============================================================================

testVariableEnvironmentV2 :: IO ()
testVariableEnvironmentV2 = do
  putStrLn "\n🔗 V2 VARIABLE ENVIRONMENT TESTING"
  putStrLn "Testing variable scoping and self-reference detection...\n"
  
  let variableTests = [
        ("Simple let", simpleLet),
        ("Nested let", nestedLet),
        ("Complex with vars", complexWithVars),
        ("Self-reference", EVLet "x" (EVVar "x") (EVVar "x")),
        ("Mutual reference", EVLet "a" (EVVar "b") (EVLet "b" (EVVar "a") (EVVar "a"))),
        ("Undefined variable", EVAdd (EVVar "undefined") (EVNum 42)),
        ("Variable shadow", EVLet "x" (EVNum 1) (EVLet "x" (EVNum 2) (EVVar "x")))
      ]
  
  putStrLn "V2 Variable environment tests:"
  mapM_ (\(name, expr) -> do
    let (v, u) = runThermo expr
    let resultStr = case v of
          VTNum n -> show n
          VTVoid (VInfo e t src) -> "VOID{e=" ++ show e ++ ",src=" ++ show src ++ "}"
          VTBool b -> show b
    
    putStrLn $ "  " ++ name ++ ": " ++ resultStr ++ 
               " (entropy=" ++ show (totalEntropy u) ++ ")"
    ) variableTests

-- ============================================================================
-- THERMODYNAMIC PROPERTIES TESTING (V2)
-- ============================================================================

testThermodynamicPropertiesV2 :: IO ()
testThermodynamicPropertiesV2 = do
  putStrLn "\n🌡️ V2 THERMODYNAMIC PROPERTIES TESTING"
  putStrLn "Testing universe evolution and entropy accumulation...\n"
  
  -- Test entropy accumulation patterns
  let entropyTests = [
        ("Single void", EVDiv (EVNum 1) (EVNum 0)),
        ("Double void", EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVDiv (EVNum 2) (EVNum 0))),
        ("Triple void", EVAdd (EVAdd (EVDiv (EVNum 1) (EVNum 0)) (EVDiv (EVNum 2) (EVNum 0))) (EVDiv (EVNum 3) (EVNum 0))),
        ("Void cascade", EVAdd (EVDiv (EVNum 100) (EVNum 0)) (EVAdd (EVVar "undefined") (EVMod (EVNum 50) (EVNum 0)))),
        ("Complex entropy", demoEntropy)
      ]
  
  putStrLn "V2 Entropy accumulation patterns:"
  mapM_ (\(name, expr) -> do
    let (v, u) = runThermo expr
    putStrLn $ "  " ++ name ++ ": entropy=" ++ show (totalEntropy u) ++ 
               ", time=" ++ show (timeStep u) ++ 
               ", voids=" ++ show (voidCount u)
    
    -- Check for heat death
    when (isHeatDeath u) $
      putStrLn $ "    🔥 HEAT DEATH WARNING (entropy >= " ++ show heatDeathThreshold ++ ")"
    ) entropyTests
  
  -- Test universe evolution consistency
  putStrLn "\nV2 Universe evolution consistency:"
  let testUniverse = initialUniverse
  let testInfo = VInfo 5 0 (TypeError "test")
  let evolvedUniverse = evolveUniverse testUniverse testInfo
  
  putStrLn $ "  Initial: " ++ show testUniverse
  putStrLn $ "  After void: " ++ show evolvedUniverse
  putStrLn $ "  Time advanced: " ++ show (timeStep evolvedUniverse - timeStep testUniverse)
  putStrLn $ "  Entropy added: " ++ show (totalEntropy evolvedUniverse - totalEntropy testUniverse)

-- ============================================================================
-- COMPARISON WITH TYPESCRIPT RESULTS
-- ============================================================================

compareWithTypeScriptV2 :: IO ()
compareWithTypeScriptV2 = do
  putStrLn "\n🆚 V2 vs TYPESCRIPT COMPARISON"
  putStrLn "Testing exact cases that showed issues in TypeScript...\n"
  
  -- Test the specific cases that caused TypeScript problems
  let problematicCases = [
        ("TS Problem Depth 8", entropyBombV2 8),
        ("TS Problem Depth 10", entropyBombV2 10),
        ("TS High Entropy", foldl1 EVAdd [EVDiv (EVNum n) (EVNum 0) | n <- [1..30]])
      ]
  
  putStrLn "V2 handling of TypeScript problematic cases:"
  mapM_ (\(name, expr) -> do
    let (v, u) = runThermo expr
    putStrLn $ "  " ++ name ++ ": entropy=" ++ show (totalEntropy u) ++ 
               ", time=" ++ show (timeStep u) ++ 
               ", voids=" ++ show (voidCount u)
    
    -- Check if V2 shows same time evolution issues as TypeScript
    when (totalEntropy u > 2000 && timeStep u < voidCount u) $
      putStrLn $ "    🚨 V2 ALSO SHOWS TIME ISSUE (like TypeScript)"
    
    when (totalEntropy u > 2000 && timeStep u >= voidCount u) $
      putStrLn $ "    ✅ V2 HANDLES HIGH ENTROPY CORRECTLY (unlike TypeScript)"
    ) problematicCases

-- ============================================================================
-- MAIN STRESS TEST EXECUTION
-- ============================================================================

main :: IO ()
main = do
  putStrLn "🔬 UNRAVEL V2 COMPREHENSIVE STRESS TEST"
  putStrLn "Testing clean V2 reference to compare with TypeScript implementation"
  putStrLn "Focus: Identify improvements needed in TypeScript version\n"
  
  testEntropyBombV2
  testMathLawsV2
  testFuelMechanismV2
  testVariableEnvironmentV2
  testThermodynamicPropertiesV2
  compareWithTypeScriptV2
  
  putStrLn "\n🏆 UNRAVEL V2 STRESS TEST COMPLETE"
  
  putStrLn "\n🎯 KEY INSIGHTS FOR TYPESCRIPT IMPROVEMENT:"
  putStrLn "1. Compare V2 entropy bomb results with TypeScript"
  putStrLn "2. Note V2 fuel consumption patterns vs TypeScript"
  putStrLn "3. Analyze V2 thermodynamic evolution vs TypeScript time issues"
  putStrLn "4. Check V2 mathematical law compliance vs TypeScript"
  putStrLn "5. Identify specific areas where TypeScript needs improvement"
  
  putStrLn "\n🔍 INVESTIGATION FOCUS:"
  putStrLn "• Does V2 show time evolution issues like TypeScript?"
  putStrLn "• How does V2 handle high entropy scenarios?"
  putStrLn "• What fuel patterns does V2 use vs TypeScript?"
  putStrLn "• Where should TypeScript implementation be improved?"
  
  putStrLn "\n🌀 V2 reference tested - ready for comparison analysis! 🌀"