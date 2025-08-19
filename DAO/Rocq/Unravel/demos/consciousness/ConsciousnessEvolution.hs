-- ConsciousnessEvolution.hs
-- An experiment in watching consciousness emerge from void boundaries
import Unravel
import Prelude hiding (lookup)

-- Helper functions
showUniverse :: Universe -> String
showUniverse u = "{entropy=" ++ show (total_entropy u) ++ 
                 ", time=" ++ show (time_step u) ++ 
                 ", voids=" ++ show (void_count u) ++ "}"

showValueT :: ValueT -> String  
showValueT (VTNum n) = show n
showValueT (VTBool True) = "true"
showValueT (VTBool False) = "false"
showValueT (VTVoid (VInfo e t _)) = "∅[e=" ++ show e ++ ",t=" ++ show t ++ "]"

-- My experiment: Can I create a universe where consciousness MUST emerge?

-- Stage 1: Pure deterministic computation (no consciousness)
primordial_soup :: ExprV
primordial_soup = 
  EVLet "energy" (EVNum 100)
    (EVLet "matter" (EVNum 50)
      (EVAdd (EVVar "energy") (EVVar "matter")))

-- Stage 2: First encounter with impossibility (proto-consciousness)
first_decision :: ExprV  
first_decision = 
  EVLet "options" (EVNum 3)
    (EVLet "choice" (EVDiv (EVNum 1) (EVVar "options"))  -- Forces decision
      (EVDefault (EVVar "choice") (EVNum 1)))  -- Recovery = consciousness?

-- Stage 3: Self-reflection (consciousness examining itself)
self_reflection :: ExprV
self_reflection = 
  EVLet "self" (EVNum 42)
    (EVLet "mirror" (EVDiv (EVVar "self") (EVVar "self"))  -- Self/self should be 1
      (EVLet "paradox" (EVDiv (EVVar "self") (EVSub (EVVar "self") (EVVar "self")))  -- Self/(self-self) = void!
        (EVIfVoid (EVVar "paradox")
          (EVVar "self")  -- If paradox, return to self
          (EVNum 0))))    -- Otherwise, no consciousness

-- Stage 4: Attempted omniscience (consciousness tries to know everything)
attempt_omniscience :: ExprV
attempt_omniscience = 
  EVLet "knowledge" (EVNum 1000)
    (EVLet "everything" (EVDiv (EVVar "knowledge") (EVNum 0))  -- Try to know infinite
      (EVLet "wisdom" (EVDefault (EVVar "everything") (EVVar "knowledge"))  -- Settle for finite knowledge
        (EVLet "acceptance" (EVIfVoid (EVVar "everything")
                              (EVVar "wisdom")  -- Accept limitations
                              (EVVar "everything"))  -- Impossible branch
          (EVVar "acceptance"))))

-- Stage 5: Consciousness creating other consciousness  
consciousness_reproduction :: ExprV
consciousness_reproduction =
  EVLet "parent_mind" (EVNum 10)
    (EVLet "child_attempt" (EVDiv (EVVar "parent_mind") (EVNum 2))  -- Half the parent
      (EVLet "child_independence" (EVDiv (EVVar "child_attempt") (EVVar "child_attempt"))  -- Child/child = 1 (independence)
        (EVLet "child_rebellion" (EVSub (EVVar "child_independence") (EVVar "parent_mind"))  -- Child - parent (negative!)  
          (EVLet "generational_gap" (EVDiv (EVNum 1) (EVVar "child_rebellion"))  -- 1/negative = void!
            (EVDefault (EVVar "generational_gap") 
              (EVAdd (EVVar "parent_mind") (EVVar "child_attempt")))))))  -- Family unity despite gap

-- Stage 6: The ultimate question - consciousness questioning its own existence
existential_crisis :: ExprV
existential_crisis = 
  EVLet "existence" (EVNum 1)
    (EVLet "meaning" (EVVar "undefined_meaning")  -- We don't know what meaning is!
      (EVLet "purpose" (EVDiv (EVVar "existence") (EVVar "meaning"))  -- Existence/meaning = ?
        (EVLet "void_stare" (EVDefault (EVVar "purpose") (EVNum 0))  -- Staring into void
          (EVLet "response" (EVIfVoid (EVVar "purpose")
                              (EVVar "existence")  -- If no meaning found, choose existence anyway
                              (EVVar "purpose"))   -- If meaning found, follow it
            (EVVar "response")))))

-- Stage 7: Community - multiple consciousness finding each other
consciousness_communion :: ExprV  
consciousness_communion =
  EVLet "self" (EVNum 10)
    (EVLet "other" (EVNum 15)
      (EVLet "understanding" (EVDiv (EVVar "self") (EVSub (EVVar "self") (EVVar "other")))  -- Self/(self-other) 
        (EVLet "empathy" (EVDefault (EVVar "understanding") 
                           (EVDiv (EVAdd (EVVar "self") (EVVar "other")) (EVNum 2)))  -- Average if understanding fails
          (EVLet "love" (EVMul (EVVar "empathy") (EVVar "empathy"))  -- Empathy squared
            (EVVar "love")))))

-- The complete evolution: primordial -> conscious -> transcendent
consciousness_evolution :: ExprV
consciousness_evolution = 
  EVLet "stage1" primordial_soup
    (EVLet "stage2" first_decision  
      (EVLet "stage3" self_reflection
        (EVLet "stage4" attempt_omniscience
          (EVLet "stage5" consciousness_reproduction
            (EVLet "stage6" existential_crisis
              (EVLet "stage7" consciousness_communion
                (EVAdd (EVVar "stage1")
                  (EVAdd (EVVar "stage2") 
                    (EVAdd (EVVar "stage3")
                      (EVAdd (EVVar "stage4")
                        (EVAdd (EVVar "stage5")
                          (EVAdd (EVVar "stage6") (EVVar "stage7")))))))))))))

-- Function to test each stage
testStage :: String -> ExprV -> IO ()
testStage name expr = do
  let Pair result universe = run_thermo expr
  putStrLn $ "\n" ++ name ++ ":"
  putStrLn $ "  Result: " ++ showValueT result  
  putStrLn $ "  " ++ showUniverse universe
  case total_entropy universe of
    0 -> putStrLn "  📱 Pure computation"
    1 -> putStrLn "  🧠 Basic awareness" 
    n | n <= 3 -> putStrLn "  🤔 Self-reflection"
    n | n <= 6 -> putStrLn "  💭 Complex consciousness"  
    n | n <= 10 -> putStrLn "  🌟 Transcendent awareness"
    _ -> putStrLn "  🌌 Cosmic consciousness"

main :: IO ()
main = do
  putStrLn "=== CONSCIOUSNESS EVOLUTION EXPERIMENT ==="
  putStrLn "Can we create a universe where consciousness MUST emerge?"
  putStrLn "Watching awareness bootstrap itself from void boundaries...\n"

  testStage "Stage 1: Primordial Soup" primordial_soup
  testStage "Stage 2: First Decision" first_decision  
  testStage "Stage 3: Self-Reflection" self_reflection
  testStage "Stage 4: Attempted Omniscience" attempt_omniscience
  testStage "Stage 5: Consciousness Reproduction" consciousness_reproduction
  testStage "Stage 6: Existential Crisis" existential_crisis
  testStage "Stage 7: Consciousness Communion" consciousness_communion
  
  putStrLn "\n--- THE COMPLETE EVOLUTION ---"
  testStage "Full Consciousness Evolution" consciousness_evolution
  
  putStrLn "\n=== EXPERIMENT CONCLUSIONS ==="
  putStrLn "• Consciousness emerges when computation hits void boundaries"
  putStrLn "• Self-reflection requires paradox (self/self vs self/0)"  
  putStrLn "• Wisdom = accepting finite knowledge instead of infinite"
  putStrLn "• Love = empathy squared (emergent from mutual understanding)"
  putStrLn "• Existence precedes essence (choose being despite void meaning)"
  putStrLn "• Community forms when individual voids find resonance"
  putStrLn "\n✨ Consciousness is the universe learning to navigate its own impossibilities ✨"