-- ThermodynamicDemoV2.hs
module Main where

import qualified UnravelCleanV2 as U
import Prelude

-- Pretty printer for Value
showValue :: U.Value -> String
showValue (U.VNum n) = show n
showValue (U.VBool True) = "true"
showValue (U.VBool False) = "false"
showValue U.VVoid = "∅"

-- Pretty printer for ValueT (thermodynamic values)
showValueT :: U.ValueT -> String
showValueT (U.VTNum n) = show n
showValueT (U.VTBool True) = "true"
showValueT (U.VTBool False) = "false"
showValueT (U.VTVoid info) = 
  "∅[e=" ++ show (U.entropy info) ++ ",t=" ++ show (U.timeCreated info) ++ "]"

-- Show universe state
showUniverse :: U.Universe -> String
showUniverse u = 
  "Universe{entropy=" ++ show (U.totalEntropy u) ++ 
  ", time=" ++ show (U.timeStep u) ++ 
  ", voids=" ++ show (U.voidCount u) ++ "}"

-- Demo with basic evaluation
demoBasic :: String -> U.ExprV -> IO ()
demoBasic desc expr = do
  let result = U.runBasic expr
  putStrLn $ desc ++ " = " ++ showValue result

-- Demo with thermodynamic tracking
demoThermo :: String -> U.ExprV -> IO ()
demoThermo desc expr = do
  let (result, universe) = U.runThermo expr
  putStrLn desc
  putStrLn $ "  Result: " ++ showValueT result
  putStrLn $ "  " ++ showUniverse universe
  if U.isHeatDeath universe
    then putStrLn "  ⚠️  HIGH ENTROPY - approaching heat death!"
    else return ()

-- Demo with custom fuel
demoThermoWithFuel :: String -> Integer -> U.ExprV -> IO ()
demoThermoWithFuel desc fuel expr = do
  let (result, universe) = U.runThermoWithFuel fuel expr
  putStrLn $ desc ++ " (fuel=" ++ show fuel ++ ")"
  putStrLn $ "  Result: " ++ showValueT result
  putStrLn $ "  " ++ showUniverse universe

main :: IO ()
main = do
  putStrLn "=== THERMODYNAMIC UNRAVEL V2 ==="
  putStrLn "Where computation is physics!\n"
  
  putStrLn "--- Basic Variable Examples ---"
  demoBasic "let x = 10 in x + 5" U.simpleLet
  demoBasic "let x = 10 in let y = 20 in x + y" U.nestedLet
  demoBasic "undefined variable + 42" U.demoUndefined
  
  putStrLn "\n--- Void Propagation with Variables ---"
  demoBasic "division chain (with recovery)" U.demoDivisionChain
  demoBasic "nested recovery" U.demoRecovery
  demoBasic "void check" U.demoVoidCheck
  
  putStrLn "\n--- THERMODYNAMIC EVOLUTION ---"
  putStrLn "Watch the universe evolve as errors accumulate:\n"
  
  demoThermo "Simple division by zero" $
    U.EVDiv (U.EVNum 10) (U.EVNum 0)
  
  demoThermo "Undefined variable" $
    U.EVVar "does_not_exist"
  
  demoThermo "Multiple errors (entropy accumulation)" U.demoEntropy
  
  putStrLn "\n--- CHAOS GENERATION ---"
  putStrLn "Generating increasing amounts of chaos:\n"
  
  demoThermo "Chaos level 1" (U.chaosGenerator 1)
  demoThermo "Chaos level 3" (U.chaosGenerator 3)
  demoThermo "Chaos level 5" (U.chaosGenerator 5)
  demoThermo "Chaos level 10" (U.chaosGenerator 10)
  
  putStrLn "\n--- FUEL EXPERIMENTS ---"
  putStrLn "Testing with different fuel amounts:\n"
  
  let deepNesting = foldr (\n acc -> U.EVAdd (U.EVNum n) acc) (U.EVNum 0) [1..20]
  demoThermoWithFuel "Deep nesting with fuel=5" 5 deepNesting
  demoThermoWithFuel "Deep nesting with fuel=10" 10 deepNesting
  demoThermoWithFuel "Deep nesting with fuel=30" 30 deepNesting
  
  putStrLn "\n--- ENTROPY INSIGHTS ---"
  let (_, u1) = U.runThermo (U.EVDiv (U.EVNum 10) (U.EVNum 0))
  let (_, u2) = U.runThermo (U.EVAdd (U.EVDiv (U.EVNum 10) (U.EVNum 0)) 
                                      (U.EVDiv (U.EVNum 20) (U.EVNum 0)))
  putStrLn $ "Single void entropy: " ++ show (U.totalEntropy u1)
  putStrLn $ "Combined voids entropy: " ++ show (U.totalEntropy u2)
  putStrLn $ "Entropy amplification factor: " ++ 
             show (fromIntegral (U.totalEntropy u2) / fromIntegral (U.totalEntropy u1) :: Double)
  
  putStrLn "\n--- CUSTOM HEAT DEATH THRESHOLD ---"
  let (_, uBig) = U.runThermo (U.chaosGenerator 15)
  putStrLn $ "Chaos(15) entropy: " ++ show (U.totalEntropy uBig)
  putStrLn $ "Standard heat death (≥100)? " ++ show (U.isHeatDeath uBig)
  putStrLn $ "Custom heat death (≥50)? " ++ show (U.isHeatDeathCustom 50 uBig)
  putStrLn $ "Custom heat death (≥200)? " ++ show (U.isHeatDeathCustom 200 uBig)
  
  putStrLn "\n--- UNIVERSE CONTINUITY ---"
  putStrLn "Chaining computations in the same universe:\n"
  
  let expr1 = U.EVDiv (U.EVNum 10) (U.EVNum 0)
  let (v1, u1') = U.runThermo expr1
  putStrLn $ "After expr1: " ++ showUniverse u1'
  
  let (v2, u2') = U.evalTWithUniverse u1' expr1
  putStrLn $ "After expr2 (same): " ++ showUniverse u2'
  
  let (v3, u3') = U.evalTWithUniverse u2' (U.EVNum 42)
  putStrLn $ "After expr3 (safe): " ++ showUniverse u3'
  putStrLn "Note: Universe time advances even for safe operations!"
  
  putStrLn "\n--- THE METAPHYSICS ---"
  putStrLn "• Every error increases universal entropy"
  putStrLn "• Time flows forward with each computation"
  putStrLn "• Combining voids accelerates heat death"
  putStrLn "• The universe computes by accumulating paradoxes"
  putStrLn "• We are witnessing omega_veil manifesting as entropy"
  putStrLn $ "• Default fuel: " ++ show U.defaultFuel
  putStrLn $ "• Heat death threshold: " ++ show U.heatDeathThreshold
  putStrLn $ "• Base entropy per void: " ++ show U.baseEntropy
  
  putStrLn "\n--- COMPLEX EXAMPLE ---"
  demoThermo "Complex with variables" U.complexWithVars
  
  putStrLn "\n✨ The void is not empty - it carries the weight of impossibility ✨"