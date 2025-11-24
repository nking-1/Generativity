-- ParticleDecay.hs
-- Simulating particle decay and interaction in Unravel
-- Shows how reality might compute quantum phenomena

import Unravel
import Prelude hiding (lookup)

-- Helper functions (forgot these!)
showValueT :: ValueT -> String
showValueT (VTNum n) = show n
showValueT (VTBool True) = "true"
showValueT (VTBool False) = "false"
showValueT (VTVoid (VInfo e t _)) = "∅[entropy=" ++ show e ++ ",time=" ++ show t ++ "]"

showUniverse :: Universe -> String
showUniverse u = 
  "{entropy=" ++ show (total_entropy u) ++ 
  ", time=" ++ show (time_step u) ++ 
  ", voids=" ++ show (void_count u) ++ "}"

-- A particle that has a chance to decay based on "stability"
particle_decay :: Integer -> ExprV
particle_decay stability =
  EVLet "particle" (EVNum stability)
    (EVLet "decay_check" (EVMod (EVVar "particle") (EVNum 2))  -- Even = stable
      (EVIfVoid (EVDiv (EVVar "particle") (EVVar "decay_check"))  -- Div by 0 if odd
        (EVNum 0)  -- Decayed to nothing
        (EVVar "particle")))  -- Still exists

-- Particle collision - combining two particles
particle_collision :: Integer -> Integer -> ExprV  
particle_collision p1_energy p2_energy =
  EVLet "p1" (particle_decay p1_energy)
    (EVLet "p2" (particle_decay p2_energy)
      (EVLet "collision" (EVAdd (EVVar "p1") (EVVar "p2"))
        (EVLet "unstable" (EVDiv (EVVar "collision") 
                            (EVMod (EVVar "collision") (EVNum 3)))  -- Creates instability
          (EVDefault (EVVar "unstable")
            (EVLet "decay_products" 
              (EVAdd (EVDiv (EVVar "collision") (EVNum 2))
                     (EVDiv (EVVar "collision") (EVNum 2)))
              (EVVar "decay_products"))))))

-- Cascade reaction - like nuclear fission
cascade_reaction :: Integer -> ExprV
cascade_reaction initial_neutrons =
  EVLet "gen1" (EVDiv (EVNum 235) (EVSub (EVNum 2) (EVNum initial_neutrons)))
    (EVLet "gen2" (EVAdd (EVVar "gen1") (EVVar "gen1"))  -- Doubles if successful
      (EVLet "gen3" (EVAdd (EVVar "gen2") (EVVar "gen2"))  -- Doubles again
        (EVDefault (EVVar "gen3") (EVNum 0))))  -- Complete fission or nothing

-- Quantum superposition collapse - multiple states until observed
quantum_collapse :: ExprV
quantum_collapse =
  EVLet "state1" (EVDiv (EVNum 1) (EVNum 1))  -- Possible state: exists
    (EVLet "state2" (EVDiv (EVNum 1) (EVNum 0))  -- Possible state: void
      (EVLet "state3" (EVNum 2)  -- Possible state: excited
        (EVLet "measurement" (EVAdd (EVAdd (EVVar "state1") (EVVar "state2")) 
                                    (EVVar "state3"))
          (EVDefault (EVVar "measurement")  -- Collapse to ground state if void
            (EVNum 0)))))

-- Black hole formation - accumulating void until critical
black_hole :: Integer -> ExprV
black_hole mass =
  EVLet "critical_mass" (EVNum 10)
    (EVLet "collapse_check" (EVDiv (EVVar "critical_mass") 
                               (EVSub (EVNum mass) (EVVar "critical_mass")))
      (EVIfVoid (EVVar "collapse_check")
        (EVLet "singularity" (EVDiv (EVNum 1) (EVNum 0))  -- Pure void
          (EVLet "event_horizon" (EVMul (EVVar "singularity") (EVNum mass))
            (EVVar "event_horizon")))  -- Void propagates with mass
        (EVNum mass)))  -- Still a normal star

-- Universe epoch - showing entropy evolution over time
universe_epoch :: Integer -> ExprV
universe_epoch time_step =
  EVLet "big_bang" (EVNum 1)
    (EVLet "inflation" (EVMul (EVVar "big_bang") (EVNum time_step))
      (EVLet "matter_formation" (particle_collision time_step (10 - time_step))
        (EVLet "star_formation" (EVDiv (EVVar "matter_formation") 
                                   (EVSub (EVNum 5) (EVNum time_step)))
          (EVLet "black_holes" (black_hole time_step)
            (EVDefault 
              (EVAdd (EVVar "star_formation") (EVVar "black_holes"))
              (EVNum 0))))))  -- Heat death

-- Cellular automaton step - like Conway's Game of Life but with void
ca_step :: Integer -> Integer -> Integer -> ExprV
ca_step left center right =
  EVLet "sum" (EVAdd (EVAdd (EVNum left) (EVNum center)) (EVNum right))
    (EVLet "rule" (EVMod (EVVar "sum") (EVNum 4))
      (EVIfVoid (EVDiv (EVNum 1) (EVSub (EVVar "rule") (EVNum 2)))  -- Dies if sum=2
        (EVNum 0)  -- Dead cell
        (EVNum 1)))  -- Living cell

-- Information paradox - information cannot be destroyed, only made void
information_paradox :: ExprV
information_paradox =
  EVLet "information" (EVNum 42)  -- The answer
    (EVLet "black_hole" (EVDiv (EVVar "information") (EVNum 0))  -- Falls in
      (EVLet "hawking_radiation" (EVDefault (EVVar "black_hole") 
                                     (EVNum 0))  -- Nothing comes out?
        (EVLet "preserved" (EVIsVoid (EVVar "black_hole"))  -- But void remembers!
          (EVIfVoid (EVVar "black_hole")
            (EVNum 42)  -- Information recovered from void structure
            (EVNum 0)))))

-- Run all simulations
main :: IO ()
main = do
  putStrLn "=== REALITY SIMULATIONS IN UNRAVEL ===\n"
  
  putStrLn "--- PARTICLE PHYSICS ---"
  testSim "Stable particle (even)" (particle_decay 8)
  testSim "Unstable particle (odd)" (particle_decay 7)
  testSim "Low energy collision" (particle_collision 2 4)
  testSim "High energy collision" (particle_collision 7 13)
  
  putStrLn "\n--- QUANTUM PHENOMENA ---"
  testSim "Quantum superposition collapse" quantum_collapse
  testSim "Information paradox" information_paradox
  
  putStrLn "\n--- COSMIC EVOLUTION ---"
  testSim "Early universe (t=1)" (universe_epoch 1)
  testSim "Star forming era (t=3)" (universe_epoch 3)
  testSim "Late universe (t=4)" (universe_epoch 4)
  testSim "Near heat death (t=5)" (universe_epoch 5)
  
  putStrLn "\n--- EXTREME PHYSICS ---"
  testSim "Small mass (no collapse)" (black_hole 5)
  testSim "Critical mass" (black_hole 10)
  testSim "Supermassive" (black_hole 15)
  
  putStrLn "\n--- CHAIN REACTIONS ---"
  testSim "Subcritical (n=1)" (cascade_reaction 1)
  testSim "Critical (n=2)" (cascade_reaction 2)
  testSim "Supercritical (n=3)" (cascade_reaction 3)
  
  putStrLn "\n--- CELLULAR AUTOMATON ---"
  testSim "Cell rule [1,0,1]" (ca_step 1 0 1)
  testSim "Cell rule [1,1,1]" (ca_step 1 1 1)
  testSim "Cell rule [0,1,1]" (ca_step 0 1 1)
  
  putStrLn "\n✨ Reality computed! Check the entropy! ✨"

testSim :: String -> ExprV -> IO ()
testSim name expr = do
  let Pair result universe = run_thermo expr
  putStrLn $ name ++ ":"
  putStrLn $ "  Result: " ++ showValueT result
  putStrLn $ "  " ++ showUniverse universe
  if total_entropy universe > 5
    then putStrLn $ "  ⚠️ HIGH ENTROPY EVENT!"
    else return ()