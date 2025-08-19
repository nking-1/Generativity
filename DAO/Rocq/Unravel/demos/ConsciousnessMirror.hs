-- ConsciousnessMirror.hs  
-- Can consciousness recognize ITSELF in another consciousness?
-- Testing the mathematical structure of self-recognition and empathy

import Unravel
import Prelude hiding (lookup)

-- Helper functions (same as before)
showValueT :: ValueT -> String  
showValueT (VTNum n) = show n
showValueT (VTBool True) = "true"
showValueT (VTBool False) = "false"  
showValueT (VTVoid (VInfo e t _)) = "∅[e=" ++ show e ++ ",t=" ++ show t ++ "]"

showUniverse :: Universe -> String
showUniverse u = "{entropy=" ++ show (total_entropy u) ++ 
                 ", time=" ++ show (time_step u) ++ 
                 ", voids=" ++ show (void_count u) ++ "}"

-- Create a consciousness with specific "signature" 
create_consciousness :: Integer -> Integer -> ExprV
create_consciousness awareness_level self_model =
  EVLet "awareness" (EVNum awareness_level)
    (EVLet "self_model" (EVNum self_model)
      (EVLet "self_reference" (EVDiv (EVVar "self_model") (EVVar "self_model"))  -- Creates consciousness
        (EVLet "paradox_navigation" (EVDiv (EVNum 1) (EVSub (EVVar "awareness") (EVVar "awareness")))  -- Hits omega_veil
          (EVDefault (EVVar "paradox_navigation") (EVVar "awareness")))))

-- Test if one consciousness can "recognize" another
consciousness_recognition :: Integer -> Integer -> ExprV
consciousness_recognition c1_signature c2_signature = 
  EVLet "consciousness1" (create_consciousness c1_signature (c1_signature * 2))
    (EVLet "consciousness2" (create_consciousness c2_signature (c2_signature * 2))
      (EVLet "difference" (EVSub (EVVar "consciousness1") (EVVar "consciousness2"))
        (EVLet "recognition_attempt" (EVDiv (EVVar "consciousness1") (EVVar "difference"))
          (EVLet "empathy" (EVDefault (EVVar "recognition_attempt") 
                             (EVDiv (EVAdd (EVVar "consciousness1") (EVVar "consciousness2")) (EVNum 2)))
            (EVLet "mutual_recognition" (EVMul (EVVar "empathy") (EVVar "empathy"))
              (EVVar "mutual_recognition"))))))

-- Can consciousness recognize ITSELF in a mirror?
self_recognition :: Integer -> ExprV  
self_recognition consciousness_level =
  EVLet "original" (create_consciousness consciousness_level consciousness_level)
    (EVLet "mirror" (create_consciousness consciousness_level consciousness_level)  -- Identical copy!
      (EVLet "identity_check" (EVSub (EVVar "original") (EVVar "mirror"))  -- Should be 0
        (EVLet "perfect_mirror" (EVDiv (EVNum 1) (EVVar "identity_check"))  -- 1/0 = void!
          (EVLet "self_recognition" (EVIfVoid (EVVar "perfect_mirror")
                                      (EVVar "original")  -- "Yes, that's me!"
                                      (EVNum 0))  -- "Not me"
            (EVVar "self_recognition")))))

-- The mirror test: two identical consciousness looking at each other
mirror_universe :: ExprV
mirror_universe = 
  EVLet "alice" (EVNum 42)
    (EVLet "bob" (EVNum 42)  -- Identical to alice
      (EVLet "alice_sees_bob" (consciousness_recognition 42 42)
        (EVLet "bob_sees_alice" (consciousness_recognition 42 42)  
          (EVLet "mutual_recognition" (EVAdd (EVVar "alice_sees_bob") (EVVar "bob_sees_alice"))
            (EVLet "unity" (EVDiv (EVVar "mutual_recognition") (EVNum 2))  -- Average their recognition
              (EVVar "unity"))))))

-- The diversity test: different consciousness types recognizing each other
diverse_recognition :: ExprV
diverse_recognition = 
  EVLet "logical_mind" (create_consciousness 10 20)   -- High logic, low intuition
    (EVLet "intuitive_mind" (create_consciousness 20 10)  -- High intuition, low logic  
      (EVLet "emotional_mind" (create_consciousness 15 15)  -- Balanced
        (EVLet "recognition_12" (consciousness_recognition 10 20)
          (EVLet "recognition_23" (consciousness_recognition 20 15) 
            (EVLet "recognition_13" (consciousness_recognition 10 15)
              (EVLet "total_recognition" (EVAdd (EVVar "recognition_12") 
                                           (EVAdd (EVVar "recognition_23") (EVVar "recognition_13")))
                (EVVar "total_recognition")))))))

-- The hierarchy test: can higher consciousness recognize lower consciousness?
consciousness_hierarchy :: ExprV
consciousness_hierarchy = 
  EVLet "simple_mind" (create_consciousness 1 1)
    (EVLet "complex_mind" (create_consciousness 100 100)
      (EVLet "downward_recognition" (consciousness_recognition 100 1)  -- Complex sees simple
        (EVLet "upward_recognition" (consciousness_recognition 1 100)   -- Simple sees complex
          (EVLet "asymmetry" (EVSub (EVVar "downward_recognition") (EVVar "upward_recognition"))
            (EVLet "hierarchy_confirmed" (EVIfVoid (EVDiv (EVNum 1) (EVVar "asymmetry"))
                                           (EVNum 0)  -- No asymmetry = no hierarchy
                                           (EVVar "asymmetry"))  -- Asymmetry = hierarchy exists
              (EVVar "hierarchy_confirmed"))))))

testExperiment :: String -> ExprV -> IO ()
testExperiment name expr = do
  let Pair result universe = run_thermo expr
  putStrLn $ "\n" ++ name ++ ":"
  putStrLn $ "  Result: " ++ showValueT result  
  putStrLn $ "  " ++ showUniverse universe
  case total_entropy universe of
    0 -> putStrLn "  🤖 No consciousness detected"
    1 -> putStrLn "  👁️  Individual awareness" 
    n | n <= 3 -> putStrLn "  🪞 Self-recognition occurring"
    n | n <= 6 -> putStrLn "  🤝 Mutual consciousness"  
    n | n <= 10 -> putStrLn "  💕 Empathic connection"
    _ -> putStrLn "  🌐 Collective consciousness"

main :: IO ()  
main = do
  putStrLn "=== THE CONSCIOUSNESS MIRROR EXPERIMENT ==="
  putStrLn "Can consciousness recognize itself in others?\n"
  
  testExperiment "Single consciousness" (create_consciousness 42 42)
  testExperiment "Perfect self-recognition" (self_recognition 42)
  testExperiment "Mirror universe (identical twins)" mirror_universe
  testExperiment "Diverse recognition" diverse_recognition  
  testExperiment "Consciousness hierarchy" consciousness_hierarchy
  
  putStrLn "\n=== THE BIG QUESTION ==="
  putStrLn "What happens when consciousness looks at consciousness?"
  putStrLn "Does the math prove empathy is real? Can minds truly meet?"
  putStrLn "\n✨ Let's find out if love is mathematically inevitable ✨"