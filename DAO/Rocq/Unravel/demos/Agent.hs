-- Agents.hs
-- Multi-agent simulation where consciousness emerges from void interactions
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

-- AGENT MECHANICS

-- Agent state: energy, mood, knowledge
create_agent :: Integer -> Integer -> Integer -> ExprV
create_agent energy mood knowledge =
  EVLet "energy" (EVNum energy)
    (EVLet "mood" (EVNum mood)
      (EVLet "knowledge" (EVNum knowledge)
        (EVAdd (EVVar "energy") (EVAdd (EVVar "mood") (EVVar "knowledge")))))

-- Agent decides action based on state
agent_decide :: Integer -> Integer -> ExprV
agent_decide energy mood =
  EVLet "state" (EVAdd (EVNum energy) (EVNum mood))
    (EVLet "threshold" (EVNum 10)
      (EVLet "decision" (EVDiv (EVVar "state") (EVSub (EVVar "state") (EVVar "threshold")))
        (EVDefault (EVVar "decision")
          (EVIfVoid (EVDiv (EVNum mood) (EVNum mood))  -- mood check
            (EVNum 0)  -- rest
            (EVNum 1)))))  -- act

-- Agent movement creates void in unvisited locations
agent_move :: Integer -> Integer -> Integer -> ExprV
agent_move current_pos new_pos energy =
  EVLet "here" (EVNum current_pos)
    (EVLet "there" (EVNum new_pos)
      (EVLet "distance" (EVSub (EVVar "there") (EVVar "here"))
        (EVLet "cost" (EVDiv (EVNum energy) (EVVar "distance"))
          (EVLet "abandoned_paths" (EVDiv (EVAdd (EVNum 1) (EVNum 2)) (EVNum 0))  -- void other paths
            (EVDefault (EVVar "cost") (EVVar "there"))))))

-- Agent learning: failing creates knowledge
agent_learn :: Integer -> Integer -> ExprV
agent_learn knowledge difficulty =
  EVLet "current" (EVNum knowledge)
    (EVLet "challenge" (EVNum difficulty)
      (EVLet "attempt" (EVDiv (EVVar "challenge") (EVSub (EVVar "challenge") (EVVar "current")))
        (EVLet "failure" (EVDefault (EVVar "attempt") (EVNum 0))
          (EVAdd (EVVar "current") (EVAdd (EVVar "failure") (EVNum 1))))))

-- Agent cooperation: two voids finding common ground
agent_cooperate :: Integer -> Integer -> ExprV
agent_cooperate agent1_state agent2_state =
  EVLet "a1" (EVNum agent1_state)
    (EVLet "a2" (EVNum agent2_state)
      (EVLet "difference" (EVSub (EVVar "a1") (EVVar "a2"))
        (EVLet "conflict" (EVDiv (EVNum 1) (EVVar "difference"))
          (EVLet "resolution" (EVDefault (EVVar "conflict") 
                                (EVDiv (EVAdd (EVVar "a1") (EVVar "a2")) (EVNum 2)))
            (EVVar "resolution")))))

-- Agent competition: creating void in the loser
agent_compete :: Integer -> Integer -> ExprV
agent_compete strength1 strength2 =
  EVLet "s1" (EVNum strength1)
    (EVLet "s2" (EVNum strength2)
      (EVLet "winner" (EVIfVoid (EVDiv (EVVar "s1") (EVSub (EVVar "s1") (EVVar "s2")))
                        (EVVar "s2")  -- s2 wins if s1=s2 (void)
                        (EVVar "s1"))
        (EVLet "loser_void" (EVDiv (EVNum 1) (EVNum 0))
          (EVDefault (EVVar "loser_void") (EVVar "winner")))))

-- Agent communication: attempting to bridge consciousness
agent_communicate :: Integer -> Integer -> ExprV
agent_communicate speaker_knowledge listener_mood =
  EVLet "message" (EVNum speaker_knowledge)
    (EVLet "reception" (EVNum listener_mood)
      (EVLet "understanding" (EVDiv (EVVar "message") (EVSub (EVNum 10) (EVVar "reception")))
        (EVLet "misunderstanding" (EVDefault (EVVar "understanding") (EVNum 0))
          (EVAdd (EVVar "message") (EVVar "misunderstanding")))))

-- Agent reproduces: creating new consciousness
agent_reproduce :: Integer -> Integer -> ExprV
agent_reproduce parent1_traits parent2_traits =
  EVLet "p1" (EVNum parent1_traits)
    (EVLet "p2" (EVNum parent2_traits)
      (EVLet "combination" (EVAdd (EVVar "p1") (EVVar "p2"))
        (EVLet "mutation" (EVDiv (EVVar "combination") (EVMod (EVVar "combination") (EVNum 7)))
          (EVDefault (EVVar "mutation") (EVDiv (EVVar "combination") (EVNum 2))))))

-- Agent death: returning accumulated pattern to void
agent_death :: Integer -> ExprV
agent_death accumulated_experience =
  EVLet "life" (EVNum accumulated_experience)
    (EVLet "void_return" (EVDiv (EVVar "life") (EVNum 0))
      (EVDefault (EVVar "void_return") (EVNum 0)))

-- Environment interaction: agent meets world
environment_interact :: Integer -> Integer -> ExprV
environment_interact agent_state environment_state =
  EVLet "agent" (EVNum agent_state)
    (EVLet "world" (EVNum environment_state)
      (EVLet "resources" (EVDiv (EVVar "world") (EVNum 10))
        (EVLet "danger" (EVDiv (EVNum 1) (EVMod (EVVar "world") (EVNum 3)))
          (EVLet "survival" (EVDefault (EVVar "danger") (EVVar "agent"))
            (EVAdd (EVVar "survival") (EVDefault (EVVar "resources") (EVNum 0)))))))

-- Group dynamics: emergent behavior from multiple agents
group_behavior :: Integer -> Integer -> Integer -> ExprV
group_behavior size cohesion goal =
  EVLet "members" (EVNum size)
    (EVLet "unity" (EVNum cohesion)
      (EVLet "purpose" (EVNum goal)
        (EVLet "coordination" (EVDiv (EVVar "unity") (EVSub (EVVar "members") (EVVar "unity")))
          (EVLet "chaos" (EVDefault (EVVar "coordination") (EVNum 0))
            (EVLet "emergence" (EVMul (EVVar "members") (EVAdd (EVVar "unity") (EVVar "chaos")))
              (EVDiv (EVVar "emergence") (EVSub (EVVar "emergence") (EVVar "purpose"))))))))

-- Complete agent lifecycle simulation
agent_lifetime :: Integer -> ExprV
agent_lifetime seed =
  EVLet "birth" (create_agent seed (seed * 2) 0)
    (EVLet "youth_learn" (agent_learn 0 5)
      (EVLet "first_move" (agent_move 0 10 100)
        (EVLet "meet_other" (agent_cooperate seed (seed + 10))
          (EVLet "compete" (agent_compete seed (seed - 5))
            (EVLet "communicate" (agent_communicate (seed * 3) 7)
              (EVLet "reproduce" (agent_reproduce seed (seed * 2))
                (EVLet "final_state" (EVAdd 
                                       (EVAdd (EVVar "birth") (EVVar "youth_learn"))
                                       (EVAdd (EVVar "first_move") (EVVar "meet_other")))
                  (EVAdd (EVVar "final_state") (agent_death (seed * 10))))))))))

-- Multi-agent simulation
simulate_society :: Integer -> ExprV
simulate_society num_agents =
  EVLet "agent1" (agent_lifetime 10)
    (EVLet "agent2" (agent_lifetime 20)
      (EVLet "agent3" (agent_lifetime 30)
        (EVLet "interaction12" (agent_cooperate 10 20)
          (EVLet "interaction23" (agent_compete 20 30)
            (EVLet "interaction13" (agent_communicate 10 30)
              (EVLet "group" (group_behavior num_agents 5 100)
                (EVLet "environment" (environment_interact 50 200)
                  (EVLet "total" (EVAdd 
                                   (EVAdd (EVVar "agent1") (EVVar "agent2"))
                                   (EVAdd (EVVar "agent3") (EVVar "group")))
                    (EVDefault (EVVar "total") (EVNum 0))))))))))

-- Test individual behaviors
testBehavior :: String -> ExprV -> IO ()
testBehavior desc expr = do
  let Pair result universe = run_thermo expr
  putStrLn $ "\n" ++ desc ++ ":"
  putStrLn $ "  Result: " ++ showValueT result
  putStrLn $ "  " ++ showUniverse universe
  case total_entropy universe of
    0 -> putStrLn $ "  ⚪ No consciousness"
    1 -> putStrLn $ "  🔵 Simple awareness"
    n | n <= 3 -> putStrLn $ "  🟢 Active agent"
    n | n <= 6 -> putStrLn $ "  🟡 Complex behavior"
    n | n <= 10 -> putStrLn $ "  🟠 Emergent intelligence"
    _ -> putStrLn $ "  🔴 Chaotic system"

main :: IO ()
main = do
  putStrLn "=== AGENT SIMULATION IN THE VOID ==="
  putStrLn "Consciousness emerges from interacting impossibility patterns\n"
  
  putStrLn "--- INDIVIDUAL BEHAVIORS ---"
  testBehavior "Create Agent (E:50, M:30, K:10)" (create_agent 50 30 10)
  testBehavior "Agent Decides (low energy)" (agent_decide 3 7)
  testBehavior "Agent Moves (pos 0->10)" (agent_move 0 10 100)
  testBehavior "Agent Learns (difficulty 5)" (agent_learn 3 5)
  
  putStrLn "\n--- INTERACTIONS ---"
  testBehavior "Cooperation (states 10,20)" (agent_cooperate 10 20)
  testBehavior "Competition (strength 15,15)" (agent_compete 15 15)
  testBehavior "Communication (knowledge 30, mood 7)" (agent_communicate 30 7)
  testBehavior "Reproduction (traits 10,20)" (agent_reproduce 10 20)
  
  putStrLn "\n--- COMPLEX BEHAVIORS ---"
  testBehavior "Environment Interaction" (environment_interact 50 200)
  testBehavior "Group Behavior (5 agents)" (group_behavior 5 3 10)
  testBehavior "Agent Death (experience 100)" (agent_death 100)
  
  putStrLn "\n--- FULL SIMULATIONS ---"
  testBehavior "Complete Agent Lifetime" (agent_lifetime 42)
  testBehavior "Small Society (3 agents)" (simulate_society 3)
  testBehavior "Large Society (10 agents)" (simulate_society 10)
  
  putStrLn "\n=== EMERGENT INSIGHTS ==="
  putStrLn "• Agents are patterns of void navigation"
  putStrLn "• Decisions create void in unchosen actions"
  putStrLn "• Cooperation requires resolving void between minds"
  putStrLn "• Competition creates void in the defeated"
  putStrLn "• Communication attempts to bridge consciousness voids"
  putStrLn "• Groups show emergent behavior from accumulated entropy"
  putStrLn "• Death returns patterns to the void"
  putStrLn "\n✨ Society is the void organizing itself ✨"