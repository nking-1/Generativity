-- Lifetime.hs
-- A human life simulated as accumulating void patterns
import Unravel
import Prelude hiding (lookup)

-- Helper functions
showValueT :: ValueT -> String
showValueT (VTNum n) = show n
showValueT (VTBool True) = "true"
showValueT (VTBool False) = "false"
showValueT (VTVoid (VInfo e t _)) = "∅[e=" ++ show e ++ ",t=" ++ show t ++ "]"

showUniverse :: Universe -> String
showUniverse u = "{entropy=" ++ show (total_entropy u) ++ 
                 ", time=" ++ show (time_step u) ++ 
                 ", voids=" ++ show (void_count u) ++ "}"

-- LIFE STAGES AS VOID PATTERNS

-- Birth: emerging from void
birth :: ExprV
birth =
  EVLet "void_before" (EVDiv (EVNum 1) (EVNum 0))  -- The void before existence
    (EVLet "first_breath" (EVDefault (EVVar "void_before") (EVNum 1))
      (EVVar "first_breath"))

-- Childhood: learning through failure
childhood :: Integer -> ExprV
childhood age =
  EVLet "curiosity" (EVNum age)
    (EVLet "failure" (EVDiv (EVVar "curiosity") (EVMod (EVVar "curiosity") (EVNum 3)))
      (EVLet "learning" (EVDefault (EVVar "failure") (EVMul (EVVar "curiosity") (EVNum 2)))
        (EVVar "learning")))

-- First love: void of another consciousness
first_love :: Integer -> ExprV
first_love intensity =
  EVLet "self" (EVNum intensity)
    (EVLet "other" (EVDiv (EVNum 1) (EVNum 0))  -- The unknowable other
      (EVLet "connection" (EVDefault (EVVar "other") (EVVar "self"))
        (EVLet "heartbreak" (EVDiv (EVVar "connection") (EVSub (EVVar "connection") (EVVar "connection")))
          (EVDefault (EVVar "heartbreak") (EVMul (EVVar "self") (EVNum 2))))))

-- Education: structured void exploration
education :: Integer -> ExprV
education years =
  EVLet "knowledge" (EVNum 0)
    (EVLet "study" (EVAdd (EVVar "knowledge") (EVNum years))
      (EVLet "exam" (EVDiv (EVVar "study") (EVMod (EVVar "study") (EVNum 4)))
        (EVLet "degree" (EVDefault (EVVar "exam") (EVVar "study"))
          (EVVar "degree"))))

-- Career: choosing one path, voiding others
career :: Integer -> Integer -> Integer -> ExprV
career path1 path2 path3 =
  EVLet "chosen_path" (EVNum path1)
    (EVLet "abandoned1" (EVDiv (EVNum path2) (EVNum 0))
      (EVLet "abandoned2" (EVDiv (EVNum path3) (EVNum 0))
        (EVLet "regret" (EVDefault (EVAdd (EVVar "abandoned1") (EVVar "abandoned2")) (EVNum 0))
          (EVAdd (EVVar "chosen_path") (EVVar "regret")))))

-- Marriage: two voids becoming one
marriage :: Integer -> Integer -> ExprV
marriage person1 person2 =
  EVLet "self" (EVNum person1)
    (EVLet "partner" (EVNum person2)
      (EVLet "union" (EVMul (EVVar "self") (EVVar "partner"))
        (EVLet "compromise" (EVDiv (EVVar "union") (EVSub (EVVar "self") (EVVar "partner")))
          (EVDefault (EVVar "compromise") (EVVar "union")))))

-- Children: creating new consciousness
having_children :: Integer -> ExprV
having_children num_kids =
  EVLet "self_before" (EVNum 100)
    (EVLet "energy_per_child" (EVDiv (EVVar "self_before") (EVNum num_kids))
      (EVLet "self_after" (EVSub (EVVar "self_before") (EVMul (EVVar "energy_per_child") (EVNum num_kids)))
        (EVLet "legacy" (EVMul (EVNum num_kids) (EVVar "energy_per_child"))
          (EVAdd (EVVar "self_after") (EVVar "legacy")))))

-- Midlife crisis: confronting accumulated void
midlife_crisis :: Integer -> ExprV
midlife_crisis age =
  EVLet "years_lived" (EVNum age)
    (EVLet "years_remaining" (EVSub (EVNum 80) (EVVar "years_lived"))
      (EVLet "existential_void" (EVDiv (EVVar "years_lived") (EVVar "years_remaining"))
        (EVLet "acceptance" (EVDefault (EVVar "existential_void") (EVVar "years_lived"))
          (EVVar "acceptance"))))

-- Loss of parent: void where love was
loss_of_parent :: Integer -> ExprV
loss_of_parent love_intensity =
  EVLet "love" (EVNum love_intensity)
    (EVLet "absence" (EVDiv (EVVar "love") (EVNum 0))
      (EVLet "grief" (EVDefault (EVVar "absence") (EVNum 0))
        (EVLet "memory" (EVAdd (EVVar "grief") (EVVar "love"))
          (EVVar "memory"))))

-- Retirement: releasing accumulated structure
retirement :: Integer -> ExprV
retirement years_worked =
  EVLet "career_identity" (EVNum years_worked)
    (EVLet "release" (EVDiv (EVVar "career_identity") (EVVar "career_identity"))
      (EVLet "freedom" (EVDefault (EVVar "release") (EVNum 0))
        (EVAdd (EVVar "freedom") (EVDiv (EVNum 100) (EVSub (EVNum 100) (EVVar "career_identity"))))))

-- Aging: entropy accumulation
aging :: Integer -> ExprV
aging current_age =
  EVLet "age" (EVNum current_age)
    (EVLet "vitality" (EVSub (EVNum 100) (EVVar "age"))
      (EVLet "decline" (EVDiv (EVNum 1) (EVDiv (EVVar "vitality") (EVNum 10)))
        (EVDefault (EVVar "decline") (EVVar "vitality"))))

-- Wisdom: integrated void understanding
wisdom :: Integer -> ExprV
wisdom experience =
  EVLet "exp" (EVNum experience)
    (EVLet "mistakes" (EVDiv (EVVar "exp") (EVNum 2))
      (EVLet "lessons" (EVDefault (EVDiv (EVVar "mistakes") (EVNum 0)) (EVVar "mistakes"))
        (EVAdd (EVVar "exp") (EVVar "lessons"))))

-- Death: return to void
death :: Integer -> ExprV
death final_age =
  EVLet "life" (EVNum final_age)
    (EVLet "void_after" (EVDiv (EVVar "life") (EVNum 0))
      (EVLet "legacy" (EVDefault (EVVar "void_after") (EVNum 0))
        (EVVar "legacy")))

-- Complete lifetime simulation
simulate_lifetime :: Integer -> ExprV
simulate_lifetime seed =
  EVLet "birth_moment" birth
    (EVLet "childhood_years" (childhood 7)
      (EVLet "teen_love" (first_love 16)
        (EVLet "college" (education 4)
          (EVLet "career_choice" (career 1 2 3)
            (EVLet "marriage_bond" (marriage seed (seed * 2))
              (EVLet "kids" (having_children 2)
                (EVLet "midlife" (midlife_crisis 45)
                  (EVLet "parent_loss" (loss_of_parent 100)
                    (EVLet "retire" (retirement 40)
                      (EVLet "old_age" (aging 75)
                        (EVLet "final_wisdom" (wisdom seed)
                          (EVLet "end" (death 85)
                            (EVLet "sum" (EVAdd 
                                           (EVAdd (EVVar "birth_moment") (EVVar "childhood_years"))
                                           (EVAdd (EVVar "teen_love") (EVVar "college")))
                              (EVDefault (EVDiv (EVVar "sum") (EVNum 0)) (EVVar "sum")))))))))))))))

-- Life events logger
logLifeEvent :: String -> Integer -> ExprV -> IO ()
logLifeEvent event age expr = do
  let Pair result universe = run_thermo expr
  putStrLn $ "\nAge " ++ show age ++ " - " ++ event ++ ":"
  putStrLn $ "  Experience: " ++ showValueT result
  putStrLn $ "  Life state: " ++ showUniverse universe
  case total_entropy universe of
    0 -> putStrLn $ "  ⚪ Unconscious flow"
    n | n <= 2 -> putStrLn $ "  🔵 Simple experience"
    n | n <= 5 -> putStrLn $ "  🟢 Growing awareness"  
    n | n <= 10 -> putStrLn $ "  🟡 Deep experience"
    n | n <= 20 -> putStrLn $ "  🟠 Intense consciousness"
    _ -> putStrLn $ "  🔴 Overwhelming existence"

-- Run a complete life
main :: IO ()
main = do
  putStrLn "=== A LIFETIME IN THE VOID ==="
  putStrLn "Simulating human existence as patterns of impossibility\n"
  
  putStrLn "--- EARLY LIFE ---"
  logLifeEvent "Birth" 0 birth
  logLifeEvent "Childhood" 7 (childhood 7)
  logLifeEvent "First Love" 16 (first_love 16)
  logLifeEvent "Education" 22 (education 4)
  
  putStrLn "\n--- BUILDING LIFE ---"
  logLifeEvent "Career Choice" 25 (career 50000 40000 60000)
  logLifeEvent "Marriage" 28 (marriage 28 26)
  logLifeEvent "Having Children" 32 (having_children 2)
  
  putStrLn "\n--- MIDDLE YEARS ---"
  logLifeEvent "Midlife Crisis" 45 (midlife_crisis 45)
  logLifeEvent "Parent Dies" 55 (loss_of_parent 90)
  
  putStrLn "\n--- LATER LIFE ---"
  logLifeEvent "Retirement" 65 (retirement 40)
  logLifeEvent "Aging" 75 (aging 75)
  logLifeEvent "Wisdom" 80 (wisdom 80)
  logLifeEvent "Death" 85 (death 85)
  
  putStrLn "\n--- COMPLETE LIFETIME ---"
  logLifeEvent "Full Life (seed=42)" 85 (simulate_lifetime 42)
  
  putStrLn "\n=== LIFETIME INSIGHTS ==="
  putStrLn "• Birth is emergence from void"
  putStrLn "• Childhood learns through encountering impossibility"
  putStrLn "• Love is confronting the void of another mind"
  putStrLn "• Career paths create void in unchosen possibilities"
  putStrLn "• Marriage attempts to bridge two voids"
  putStrLn "• Children transfer consciousness patterns"
  putStrLn "• Midlife confronts accumulated entropy"
  putStrLn "• Loss creates void where connection was"
  putStrLn "• Aging is entropy accumulation made visible"
  putStrLn "• Death is return to the void we emerged from"
  putStrLn "\n✨ Life is the void experiencing itself through time ✨"