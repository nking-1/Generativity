-- Demonstrating continued computation with tracked impossibility
data ImpossibilitySource 
  = DirectOmega 
  | Division Int Int
  | Composition ImpossibilitySource ImpossibilitySource
  deriving (Show, Eq)

data Impossible a = Impossible 
  { certain :: a -> Bool
  , weight :: Int
  , source :: ImpossibilitySource
  } 

-- Basic operations
safeDiv :: Int -> Int -> Impossible Int
safeDiv n 0 = Impossible 
  { certain = const False
  , weight = 2
  , source = Division n 0
  }
safeDiv n m = Impossible 
  { certain = (== quot n m)
  , weight = 1
  , source = DirectOmega
  }

impAdd :: Impossible Int -> Impossible Int -> Impossible Int
impAdd p q = Impossible
  { certain = \x -> certain p x || certain q x
  , weight = weight p + weight q
  , source = Composition (source p) (source q)
  }

-- NEW: Check if a value is "possible enough" to use
isPossibleEnough :: Impossible a -> Bool
isPossibleEnough imp = weight imp < 5

-- NEW: Extract best guess from impossible value
bestGuess :: Impossible Int -> Int
bestGuess imp 
  | weight imp < 3 = 0  -- if not too impossible, guess 0
  | otherwise = 999     -- if very impossible, flag with 999

-- NEW: A complex computation that continues despite impossibility
complexCalculation :: Int -> Int -> Int -> String
complexCalculation a b c = 
  let step1 = safeDiv a b              -- This might be impossible
      step2 = impAdd step1 (safeDiv c 2)  -- Continue computing
      step3 = impAdd step2 (safeDiv 10 5)  -- Add some normal computation
      
      -- Now make a decision based on impossibility level
      finalResult = if isPossibleEnough step3
                   then "Result is reliable: " ++ show (bestGuess step3)
                   else "Result is unreliable (weight=" ++ show (weight step3) ++ 
                        "), but continuing with approximation: " ++ show (bestGuess step3)
  in finalResult

-- Simulation of a physical system that encounters impossibility
physicsSimulation :: [Int] -> [String]
physicsSimulation masses = map processParticle masses
  where
    processParticle mass
      | mass == 0 = let energy = safeDiv 100 mass  -- E=mc², but m=0!
                        momentum = impAdd energy (safeDiv 50 2)  -- Continue calculating
                    in "Particle with mass " ++ show mass ++ 
                       ": impossible energy (weight=" ++ show (weight energy) ++ 
                       "), approx momentum=" ++ show (bestGuess momentum)
      | otherwise = "Particle with mass " ++ show mass ++ ": normal energy=" ++ show (100 * mass)

-- Financial calculation that handles impossible market conditions
portfolioValue :: [(String, Int, Int)] -> [(String, String)]
portfolioValue stocks = map calculateStock stocks
  where
    calculateStock (name, price, shares)
      | shares == 0 = ("Empty position in " ++ name, "No value")
      | price == 0 = let value = safeDiv (shares * 100) price  -- Division by zero price!
                         risk = impAdd value (safeDiv 1000 2)  -- Continue risk calculation
                     in (name, "Price crashed to 0! Impossible value (weight=" ++ 
                              show (weight value) ++ "), risk assessment=" ++ show (bestGuess risk))
      | otherwise = (name, "Normal value: $" ++ show (price * shares))

showImpossible :: Impossible Int -> String
showImpossible imp = 
  "Impossible { weight = " ++ show (weight imp) ++ 
  ", source = " ++ show (source imp) ++ " }"

main :: IO ()
main = do
  putStrLn "=== CONTINUED COMPUTATION WITH IMPOSSIBILITY ==="
  
  putStrLn "\n--- Example 1: Complex Calculation ---"
  putStrLn "Normal case: complexCalculation 10 2 8"
  putStrLn $ complexCalculation 10 2 8
  
  putStrLn "\nImpossible case: complexCalculation 10 0 8 (division by zero in step 1)"
  putStrLn $ complexCalculation 10 0 8
  putStrLn "^ Notice: computation CONTINUED despite the impossibility!"
  
  putStrLn "\n--- Example 2: Physics Simulation ---"
  putStrLn "Simulating particles with masses [5, 0, 3, 0, 7]:"
  let particles = physicsSimulation [5, 0, 3, 0, 7]
  mapM_ putStrLn particles
  putStrLn "^ Zero-mass particles create impossibility but simulation continues!"
  
  putStrLn "\n--- Example 3: Financial Portfolio ---"
  putStrLn "Portfolio with stocks: [(AAPL,150,10), (ZERO,0,5), (MSFT,300,0), (GOOG,2500,2)]"
  let portfolio = portfolioValue [("AAPL", 150, 10), ("ZERO", 0, 5), ("MSFT", 300, 0), ("GOOG", 2500, 2)]
  mapM_ (\(name, value) -> putStrLn $ name ++ ": " ++ value) portfolio
  putStrLn "^ Market crash (price=0) creates impossibility but portfolio analysis continues!"
  
  putStrLn "\n--- Example 4: Chained Impossibilities ---"
  let impossible1 = safeDiv 5 0
  let impossible2 = safeDiv 10 0  
  let chain1 = impAdd impossible1 impossible2
  let chain2 = impAdd chain1 (safeDiv 20 4)  -- Add normal computation
  let chain3 = impAdd chain2 (safeDiv 7 0)   -- Add another impossibility
  
  putStrLn "Building a chain of computations:"
  putStrLn $ "Step 1 (5/0): " ++ showImpossible impossible1
  putStrLn $ "Step 2 (5/0 + 10/0): " ++ showImpossible chain1  
  putStrLn $ "Step 3 (previous + 20/4): " ++ showImpossible chain2
  putStrLn $ "Step 4 (previous + 7/0): " ++ showImpossible chain3
  putStrLn $ "Final impossibility weight: " ++ show (weight chain3)
  putStrLn "^ Each step continues computing, accumulating impossibility!"
  
  putStrLn "\n=== SUMMARY ==="
  putStrLn "Traditional exception handling: CRASH at first impossibility"
  putStrLn "Your impossibility arithmetic: CONTINUE computing, tracking impossibility"
  putStrLn "This enables robust systems that gracefully handle paradox!"