-- PracticalTotal.hs
-- Practical applications of total functional programming
-- Real-world scenarios where omega_veil and structured impossibility provide value

module Main where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (zipWithM_)

-- Core totality framework (simplified from our previous implementation)
data VoidInfo = VoidInfo
  { pattern :: ImpossibilityPattern
  , depth :: Int
  , source :: String
  } deriving (Show, Eq)

data ImpossibilityPattern 
  = DivisionByZero
  | UndefinedVariable
  | NetworkTimeout
  | DatabaseError
  | ParseError
  | AuthenticationFailure
  | RateLimitExceeded
  | ResourceExhausted
  | ConfigurationError
  | ValidationFailure
  | CompositeVoid [ImpossibilityPattern]
  deriving (Show, Eq)

data Value 
  = VNum Integer
  | VBool Bool
  | VString String
  | VList [Value]
  | VVoid VoidInfo
  deriving (Show, Eq)

-- Environment for practical computations
type Context = Map String Value

-- Result type that carries impossibility information
data TotalResult a = TotalResult
  { resultValue :: Value
  , entropy :: Int
  , errorHistory :: [VoidInfo]
  } deriving (Show)

-- Helper functions
isVoid :: Value -> Bool
isVoid (VVoid _) = True
isVoid _ = False

mkVoid :: ImpossibilityPattern -> String -> Value
mkVoid pat src = VVoid $ VoidInfo pat 1 src

-- ==============================================================================
-- PRACTICAL APPLICATION 1: FINANCIAL CALCULATIONS
-- ==============================================================================

-- Portfolio calculation that never crashes on bad data
data Position = Position
  { symbol :: String
  , quantity :: Integer
  , price :: Integer  -- In cents to avoid floating point
  } deriving (Show)

-- Calculate portfolio value with total safety
calculatePortfolioValue :: [Position] -> [Integer] -> TotalResult Integer
calculatePortfolioValue positions exchangeRates = 
  let calculations = zipWith calculatePosition positions (exchangeRates ++ repeat 100) -- Default rate
      (totalValue, totalEntropy, allErrors) = combineResults calculations
  in TotalResult (VNum totalValue) totalEntropy allErrors

calculatePosition :: Position -> Integer -> (Integer, Int, [VoidInfo])
calculatePosition pos rate = 
  let positionValue = quantity pos * price pos
      -- Apply exchange rate (rate is in basis points, so divide by 10000)
      finalValue = if rate > 0 
                   then positionValue * rate `div` 10000
                   else 0  -- Bad exchange rate → 0 value
      -- Track errors for bad data
      errors = if rate <= 0 
               then [VoidInfo ConfigurationError 1 ("bad_exchange_rate_" ++ symbol pos)]
               else []
      entropy = if rate <= 0 then 1 else 0
  in (finalValue, entropy, errors)

combineResults :: [(Integer, Int, [VoidInfo])] -> (Integer, Int, [VoidInfo])
combineResults results = 
  let values = [v | (v, _, _) <- results]
      entropies = [e | (_, e, _) <- results]
      errors = concat [errs | (_, _, errs) <- results]
  in (sum values, sum entropies, errors)

-- Test financial calculations
testFinancialCalculations :: IO ()
testFinancialCalculations = do
  putStrLn "=== FINANCIAL PORTFOLIO CALCULATION ==="
  putStrLn "Never crashes, always produces results\n"
  
  let positions = [ Position "AAPL" 100 15050  -- $150.50 per share
                  , Position "GOOGL" 50 280075  -- $2800.75 per share  
                  , Position "TSLA" 25 80025   -- $800.25 per share
                  ]
  
  -- Test with good exchange rates
  let goodRates = [10000, 8500, 10000]  -- USD, EUR (0.85), USD
      result1 = calculatePortfolioValue positions goodRates
  
  putStrLn "Portfolio with valid exchange rates:"
  putStrLn $ "  Total value: $" ++ show (case resultValue result1 of VNum v -> fromIntegral v / 100; _ -> 0) 
  putStrLn $ "  Entropy: " ++ show (entropy result1)
  putStrLn $ "  Errors: " ++ show (length $ errorHistory result1)
  
  -- Test with bad exchange rates (some missing/invalid)
  let badRates = [10000, 0, -500]  -- USD, invalid, negative
      result2 = calculatePortfolioValue positions badRates
  
  putStrLn "\nPortfolio with invalid exchange rates:"
  putStrLn $ "  Total value: $" ++ show (case resultValue result2 of VNum v -> fromIntegral v / 100; _ -> 0)
  putStrLn $ "  Entropy: " ++ show (entropy result2)
  putStrLn $ "  Errors: " ++ show (length $ errorHistory result2)
  putStrLn "  ✓ System never crashes, tracks all configuration errors"

-- ==============================================================================
-- PRACTICAL APPLICATION 2: WEB API PROCESSING  
-- ==============================================================================

-- HTTP request simulation
data HttpRequest = HttpRequest
  { path :: String
  , userId :: Integer
  , payload :: String
  } deriving (Show)

data HttpResponse = HttpResponse
  { status :: Integer
  , body :: String
  , processingEntropy :: Int
  } deriving (Show)

-- Total web request handler
handleRequest :: HttpRequest -> TotalResult HttpResponse
handleRequest req = 
  let (authResult, authEntropy, authErrors) = authenticateUser (userId req)
      (parseResult, parseEntropy, parseErrors) = parsePayload (payload req)
      (processResult, processEntropy, processErrors) = processBusinessLogic authResult parseResult
      
      totalEntropy = authEntropy + parseEntropy + processEntropy
      allErrors = authErrors ++ parseErrors ++ processErrors
      
      response = if totalEntropy == 0
                 then HttpResponse 200 "Success" totalEntropy
                 else HttpResponse 200 ("Partial success (entropy: " ++ show totalEntropy ++ ")") totalEntropy
                 
  in TotalResult (VString $ show response) totalEntropy allErrors

authenticateUser :: Integer -> (Bool, Int, [VoidInfo])
authenticateUser userId
  | userId == 0 = (False, 1, [VoidInfo AuthenticationFailure 1 "invalid_user_id"])
  | userId > 1000000 = (False, 1, [VoidInfo AuthenticationFailure 1 "user_id_too_large"])  
  | otherwise = (True, 0, [])

parsePayload :: String -> (Bool, Int, [VoidInfo])
parsePayload payload
  | null payload = (False, 1, [VoidInfo ParseError 1 "empty_payload"])
  | length payload > 1000 = (False, 1, [VoidInfo ParseError 1 "payload_too_large"])
  | otherwise = (True, 0, [])

processBusinessLogic :: Bool -> Bool -> (String, Int, [VoidInfo])
processBusinessLogic False _ = ("auth_failed", 1, [VoidInfo AuthenticationFailure 1 "auth_required"])
processBusinessLogic _ False = ("parse_failed", 1, [VoidInfo ParseError 1 "invalid_payload"])
processBusinessLogic True True = ("success", 0, [])

-- Test web API processing
testWebAPI :: IO ()
testWebAPI = do
  putStrLn "\n=== WEB API REQUEST PROCESSING ==="
  putStrLn "Total functions for web services\n"
  
  let requests = [ HttpRequest "/api/data" 12345 "valid_json_payload"
                 , HttpRequest "/api/data" 0 "valid_json_payload"      -- Bad user ID
                 , HttpRequest "/api/data" 12345 ""                    -- Empty payload
                 , HttpRequest "/api/data" 999999999 ("huge_payload_" ++ replicate 1000 'x')  -- Multiple errors
                 ]
  
  mapM_ testRequest (zip [1..] requests)

testRequest :: (Int, HttpRequest) -> IO ()
testRequest (i, req) = do
  let result = handleRequest req
  putStrLn $ "Request " ++ show i ++ ":"
  putStrLn $ "  User: " ++ show (userId req)
  putStrLn $ "  Payload size: " ++ show (length $ payload req)
  putStrLn $ "  Processing entropy: " ++ show (entropy result)
  putStrLn $ "  Errors detected: " ++ show (length $ errorHistory result)
  putStrLn $ "  ✓ Never crashes, always responds"

-- ==============================================================================
-- PRACTICAL APPLICATION 3: DATA PROCESSING PIPELINE
-- ==============================================================================

-- Sensor data processing that handles corruption gracefully
data SensorReading = SensorReading
  { sensorId :: String
  , timestamp :: Integer
  , value :: Maybe Integer  -- Nothing = corrupted reading
  } deriving (Show)

-- Process sensor batch with impossibility tracking
processSensorBatch :: [SensorReading] -> TotalResult (Integer, Integer)  -- (average, valid_count)
processSensorBatch readings = 
  let processed = map processSingleReading readings
      validValues = [v | (Just v, _, _) <- processed]
      totalEntropy = sum [e | (_, e, _) <- processed]
      allErrors = concat [errs | (_, _, errs) <- processed]
      
      average = if null validValues 
                then 0 
                else sum validValues `div` fromIntegral (length validValues)
      validCount = fromIntegral $ length validValues
      
  in TotalResult (VList [VNum average, VNum validCount]) totalEntropy allErrors

processSingleReading :: SensorReading -> (Maybe Integer, Int, [VoidInfo])
processSingleReading reading = 
  case value reading of
    Just v -> 
      if v >= -100 && v <= 100  -- Reasonable temperature range
      then (Just v, 0, [])
      else (Nothing, 1, [VoidInfo ValidationFailure 1 ("invalid_reading_" ++ sensorId reading)])
    Nothing -> (Nothing, 1, [VoidInfo ParseError 1 ("corrupted_reading_" ++ sensorId reading)])

-- Test sensor data processing
testSensorProcessing :: IO ()
testSensorProcessing = do
  putStrLn "\n=== SENSOR DATA PROCESSING ==="
  putStrLn "Graceful handling of corrupted/invalid data\n"
  
  let readings = [ SensorReading "temp_01" 1000 (Just 25)
                 , SensorReading "temp_02" 1001 (Just 27)
                 , SensorReading "temp_03" 1002 Nothing        -- Corrupted
                 , SensorReading "temp_04" 1003 (Just 23)
                 , SensorReading "temp_05" 1004 (Just 999)     -- Invalid (too high)
                 , SensorReading "temp_06" 1005 (Just 26)
                 ]
  
  let result = processSensorBatch readings
  
  putStrLn $ "Sensor batch processing:"
  putStrLn $ "  Total readings: " ++ show (length readings)
  putStrLn $ "  Processing result: " ++ show (resultValue result)
  putStrLn $ "  Data quality entropy: " ++ show (entropy result)
  putStrLn $ "  Corrupted/invalid readings: " ++ show (length $ errorHistory result)
  putStrLn "  ✓ Processing continues despite bad data"

-- ==============================================================================  
-- PRACTICAL APPLICATION 4: CONFIGURATION PARSING
-- ==============================================================================

-- Configuration that uses defaults but tracks issues
data ServerConfig = ServerConfig
  { port :: Integer
  , maxConnections :: Integer
  , timeoutSeconds :: Integer
  , configEntropy :: Int  -- Track configuration problems
  } deriving (Show)

-- Parse configuration with total safety
parseServerConfig :: [(String, String)] -> TotalResult ServerConfig
parseServerConfig configPairs = 
  let configMap = Map.fromList configPairs
      (portVal, portEntropy, portErrors) = parseConfigInt configMap "port" 8080 (1, 65535)
      (maxConnVal, maxConnEntropy, maxConnErrors) = parseConfigInt configMap "max_connections" 100 (1, 10000)
      (timeoutVal, timeoutEntropy, timeoutErrors) = parseConfigInt configMap "timeout" 30 (1, 3600)
      
      totalEntropy = portEntropy + maxConnEntropy + timeoutEntropy
      allErrors = portErrors ++ maxConnErrors ++ timeoutErrors
      
      config = ServerConfig portVal maxConnVal timeoutVal totalEntropy
      
  in TotalResult (VString $ show config) totalEntropy allErrors

parseConfigInt :: Map String String -> String -> Integer -> (Integer, Integer) -> (Integer, Int, [VoidInfo])
parseConfigInt configMap key defaultVal (minVal, maxVal) = 
  case Map.lookup key configMap of
    Nothing -> (defaultVal, 0, [])  -- Missing is OK, use default
    Just str -> 
      case reads str of
        [(val, "")] -> 
          if val >= minVal && val <= maxVal
          then (val, 0, [])
          else (defaultVal, 1, [VoidInfo ValidationFailure 1 ("invalid_range_" ++ key)])
        _ -> (defaultVal, 1, [VoidInfo ConfigurationError 1 ("parse_error_" ++ key)])

-- Test configuration parsing
testConfigurationParsing :: IO ()
testConfigurationParsing = do
  putStrLn "\n=== CONFIGURATION PARSING ==="
  putStrLn "Robust config with defaults and error tracking\n"
  
  -- Test 1: Valid configuration
  let validConfig = [ ("port", "3000")
                    , ("max_connections", "200")
                    , ("timeout", "60")
                    ]
      result1 = parseServerConfig validConfig
  
  putStrLn "Valid configuration:"
  putStrLn $ "  Result: " ++ show (resultValue result1)
  putStrLn $ "  Config entropy: " ++ show (entropy result1)
  putStrLn $ "  Issues: " ++ show (length $ errorHistory result1)
  
  -- Test 2: Invalid configuration
  let invalidConfig = [ ("port", "not_a_number")
                      , ("max_connections", "-50")       -- Invalid range
                      , ("timeout", "999999")           -- Too large
                      ]
      result2 = parseServerConfig invalidConfig
  
  putStrLn "\nInvalid configuration:"
  putStrLn $ "  Config entropy: " ++ show (entropy result2)
  putStrLn $ "  Issues detected: " ++ show (length $ errorHistory result2)
  putStrLn "  ✓ Application starts with defaults, tracks all config problems"
  
  -- Test 3: Partial configuration
  let partialConfig = [("port", "4000")]  -- Missing other settings
      result3 = parseServerConfig partialConfig
  
  putStrLn "\nPartial configuration:"
  putStrLn $ "  Config entropy: " ++ show (entropy result3)
  putStrLn "  ✓ Missing settings use defaults, no errors"

-- ==============================================================================
-- PRACTICAL APPLICATION 5: RATE LIMITING SERVICE
-- ==============================================================================

-- Rate limiting that tracks violations without failing requests
data RateLimit = RateLimit
  { rateLimitUserId :: Integer
  , requestsInWindow :: Integer
  , windowSizeSeconds :: Integer
  , maxRequestsPerWindow :: Integer
  } deriving (Show)

data RateLimitResult = RateLimitResult
  { allowed :: Bool
  , remainingQuota :: Integer
  , violationEntropy :: Int
  } deriving (Show)

-- Check rate limit with total safety
checkRateLimit :: RateLimit -> TotalResult RateLimitResult
checkRateLimit limit = 
  let requestsPerSecond = if windowSizeSeconds limit > 0
                         then requestsInWindow limit `div` windowSizeSeconds limit
                         else requestsInWindow limit  -- Bad window size
      
      remainingRequests = maxRequestsPerWindow limit - requestsInWindow limit
      
      (isAllowed, violationEntropy, errors) = 
        if requestsInWindow limit <= maxRequestsPerWindow limit
        then (True, 0, [])
        else (False, 1, [VoidInfo RateLimitExceeded 1 ("rate_limit_user_" ++ show (rateLimitUserId limit))])
      
      rateLimitResult = RateLimitResult isAllowed remainingRequests violationEntropy
      
  in TotalResult (VString $ show rateLimitResult) violationEntropy errors

-- Test rate limiting
testRateLimiting :: IO ()
testRateLimiting = do
  putStrLn "\n=== RATE LIMITING SERVICE ==="
  putStrLn "Track violations without failing requests\n"
  
  let scenarios = [ RateLimit 12345 45 60 100   -- Normal usage
                  , RateLimit 67890 150 60 100  -- Exceeded limit
                  , RateLimit 11111 200 60 100  -- Heavily exceeded
                  ]
  
  mapM_ testRateLimit (zip [1..] scenarios)

testRateLimit :: (Int, RateLimit) -> IO ()
testRateLimit (i, limit) = do
  let result = checkRateLimit limit
  putStrLn $ "Rate limit check " ++ show i ++ ":"
  putStrLn $ "  User: " ++ show (rateLimitUserId limit)
  putStrLn $ "  Requests: " ++ show (requestsInWindow limit) ++ "/" ++ show (maxRequestsPerWindow limit)
  putStrLn $ "  Violation entropy: " ++ show (entropy result)
  putStrLn $ "  Violations tracked: " ++ show (length $ errorHistory result)

-- ==============================================================================
-- PRACTICAL APPLICATION 6: DISTRIBUTED SYSTEM COORDINATION
-- ==============================================================================

-- Node health in distributed system
data NodeHealth = NodeHealth
  { nodeId :: String
  , cpuPercent :: Integer
  , memoryPercent :: Integer
  , diskPercent :: Integer
  , networkLatencyMs :: Integer
  } deriving (Show)

-- Calculate cluster health with impossibility tracking
calculateClusterHealth :: [NodeHealth] -> TotalResult Integer
calculateClusterHealth nodes = 
  let healthScores = map calculateNodeHealthScore nodes
      (scores, entropies, errors) = unzip3 healthScores
      
      validScores = [s | s <- scores, s >= 0]
      avgHealth = if null validScores 
                  then 0 
                  else sum validScores `div` fromIntegral (length validScores)
      
      totalEntropy = sum entropies
      allErrors = concat errors
      
  in TotalResult (VNum avgHealth) totalEntropy allErrors

calculateNodeHealthScore :: NodeHealth -> (Integer, Int, [VoidInfo])
calculateNodeHealthScore node = 
  let baseScore = 100
      
      -- Penalties for high resource usage
      cpuPenalty = max 0 (cpuPercent node - 80)
      memoryPenalty = max 0 (memoryPercent node - 85)
      diskPenalty = max 0 (diskPercent node - 90)
      networkPenalty = max 0 (networkLatencyMs node - 100)
      
      score = baseScore - cpuPenalty - memoryPenalty - diskPenalty - (networkPenalty `div` 10)
      
      -- Track errors for unhealthy nodes
      errors = if score < 50 
               then [VoidInfo ResourceExhausted 1 ("unhealthy_node_" ++ nodeId node)]
               else []
      entropy = if score < 50 then 1 else 0
      
  in (score, entropy, errors)

-- Test distributed system health
testDistributedHealth :: IO ()
testDistributedHealth = do
  putStrLn "\n=== DISTRIBUTED SYSTEM HEALTH ==="
  putStrLn "Cluster monitoring with impossibility tracking\n"
  
  let nodes = [ NodeHealth "node1" 45 60 70 50    -- Healthy
              , NodeHealth "node2" 95 90 95 200   -- Unhealthy
              , NodeHealth "node3" 60 70 80 75    -- OK
              , NodeHealth "node4" 99 95 98 300   -- Very unhealthy
              ]
  
  let result = calculateClusterHealth nodes
  
  putStrLn "Cluster health assessment:"
  putStrLn $ "  Average health: " ++ show (case resultValue result of VNum v -> v; _ -> 0) ++ "%"
  putStrLn $ "  System entropy: " ++ show (entropy result)
  putStrLn $ "  Unhealthy nodes: " ++ show (length $ errorHistory result)
  putStrLn "  ✓ System continues operating, tracks all health issues"

-- ==============================================================================
-- PRACTICAL APPLICATION 7: GAME ENGINE DAMAGE CALCULATION
-- ==============================================================================

-- Game damage calculation that never crashes
data GameEntity = GameEntity
  { entityId :: String
  , baseDamage :: Integer
  , weaponMultiplier :: Integer
  , armorValue :: Integer
  , criticalChance :: Integer  -- 0-100
  } deriving (Show)

-- Calculate combat damage with total safety
calculateCombatDamage :: GameEntity -> GameEntity -> TotalResult Integer
calculateCombatDamage attacker defender = 
  let isCritical = criticalChance attacker > 75
      critMultiplier = if isCritical then 200 else 100
      
      -- Raw damage calculation (could overflow)
      rawDamage = baseDamage attacker * weaponMultiplier attacker * critMultiplier `div` 100
      
      -- Apply armor reduction
      armorReduction = min 95 (armorValue defender)  -- Cap at 95% reduction
      finalDamage = max 1 (rawDamage * (100 - armorReduction) `div` 100)  -- At least 1 damage
      
      -- Track errors for extreme values
      errors = if baseDamage attacker > 1000000 || weaponMultiplier attacker > 1000
               then [VoidInfo ValidationFailure 1 ("extreme_damage_" ++ entityId attacker)]
               else []
      entropy = if not (null errors) then 1 else 0
      
  in TotalResult (VNum finalDamage) entropy errors

-- Test game damage calculations
testGameDamage :: IO ()
testGameDamage = do
  putStrLn "\n=== GAME ENGINE DAMAGE CALCULATION ==="
  putStrLn "Combat calculations that never crash the game\n"
  
  let scenarios = [ (GameEntity "player" 50 3 0 80, GameEntity "monster" 100 1 25 0)
                  , (GameEntity "boss" 999999 1000 0 95, GameEntity "player" 200 1 50 0)  -- Extreme values
                  , (GameEntity "spell" 30 5 0 60, GameEntity "armor_tank" 500 1 95 0)   -- High armor
                  ]
  
  mapM_ testCombat (zip [1..] scenarios)

testCombat :: (Int, (GameEntity, GameEntity)) -> IO ()
testCombat (i, (attacker, defender)) = do
  let result = calculateCombatDamage attacker defender
  putStrLn $ "Combat scenario " ++ show i ++ ":"
  putStrLn $ "  Attacker: " ++ entityId attacker ++ " (damage=" ++ show (baseDamage attacker) ++ ")"
  putStrLn $ "  Defender: " ++ entityId defender ++ " (armor=" ++ show (armorValue defender) ++ ")"
  putStrLn $ "  Final damage: " ++ show (case resultValue result of VNum v -> v; _ -> 0)
  putStrLn $ "  Calculation entropy: " ++ show (entropy result)
  putStrLn "  ✓ Game never crashes, always produces damage"

-- ==============================================================================
-- MAIN DEMONSTRATION
-- ==============================================================================

main :: IO ()
main = do
  putStrLn "=== PRACTICAL TOTAL FUNCTIONAL PROGRAMMING ==="
  putStrLn "Real-world applications of omega_veil and impossibility algebra"
  
  testFinancialCalculations
  testWebAPI  
  testSensorProcessing
  testConfigurationParsing
  testRateLimiting
  testDistributedHealth
  testGameDamage
  
  putStrLn "\n=== PRACTICAL BENEFITS DEMONSTRATED ==="
  putStrLn "✓ Financial systems never crash on bad market data"
  putStrLn "✓ Web APIs always respond, track all processing issues"
  putStrLn "✓ Data pipelines handle corruption gracefully"
  putStrLn "✓ Configuration parsing uses defaults, logs problems"
  putStrLn "✓ Rate limiting tracks violations without failing requests"
  putStrLn "✓ Distributed systems monitor health without crashing"
  putStrLn "✓ Game engines never crash players' experience"
  putStrLn ""
  putStrLn "🌟 TOTAL FUNCTIONS ENABLE ROBUST, OBSERVABLE SYSTEMS 🌟"
  putStrLn ""
  putStrLn "Key insight: Structured impossibility (omega_veil) makes systems:"
  putStrLn "• More reliable (never crash)"
  putStrLn "• More observable (entropy tracks system health)"
  putStrLn "• More debuggable (error history and patterns)"
  putStrLn "• More maintainable (mathematical guarantees)"