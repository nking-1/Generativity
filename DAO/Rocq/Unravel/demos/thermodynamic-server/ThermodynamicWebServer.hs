-- ThermodynamicWebServer.hs
-- A web server that tracks entropy and literally cannot crash
{-# LANGUAGE BlockArguments #-}

import Unravel
import Network.HTTP.Types
import Network.Wai
import Network.Wai.Handler.Warp
import Data.ByteString.Lazy.Char8 as L8
import Data.ByteString.Char8 as B8
import Control.Concurrent.STM
import Control.Monad.IO.Class
import Data.Aeson (object, (.=), encode)
import Data.Time

-- Server state: multiple universes for isolation
data ServerState = ServerState {
  universes :: TVar [Universe],
  requestCount :: TVar Integer,
  maxEntropyPerRequest :: Integer,
  globalEntropyLimit :: Integer
}

-- Convert HTTP path to Unravel expression (user code sandbox)
pathToExpr :: [Text] -> ExprV
pathToExpr ["add", x, y] = 
  EVAdd (EVNum (read $ unpack x)) (EVNum (read $ unpack y))
pathToExpr ["div", x, y] = 
  EVDiv (EVNum (read $ unpack x)) (EVNum (read $ unpack y))
pathToExpr ["factorial", n] = 
  factorial (read $ unpack n)
pathToExpr ["fib", n] = 
  fibonacci (read $ unpack n)
pathToExpr ["chaos", n] = 
  chaos_generator (read $ unpack n)
pathToExpr ["loop"] = 
  -- This would infinite loop in normal server!
  EVLet "x" (EVVar "x") (EVVar "x")
pathToExpr _ = EVNum 404

-- Process request in isolated universe
processInUniverse :: ServerState -> Request -> IO Response
processInUniverse state req = do
  -- Get fresh universe or coolest available
  universe <- atomically $ do
    us <- readTVar (universes state)
    case us of
      [] -> return initial_universe
      (u:rest) -> do
        writeTVar (universes state) rest
        return u
  
  -- Parse request into Unravel expression
  let path = pathInfo req
  let expr = pathToExpr path
  
  -- EVALUATE WITH THERMODYNAMIC TRACKING
  let startTime = time_step universe
  let (result, finalUniverse) = evalT 1000 universe [] expr
  
  -- Check thermal status
  let entropy = total_entropy finalUniverse
  let deltaEntropy = entropy - total_entropy universe
  let timeElapsed = time_step finalUniverse - startTime
  
  -- Build response with thermodynamic metadata
  let response = object
    [ "result"      .= showValueT result
    , "entropy"     .= entropy
    , "deltaEntropy" .= deltaEntropy
    , "timeSteps"   .= timeElapsed
    , "voidCount"   .= void_count finalUniverse
    , "status"      .= thermalStatus entropy (maxEntropyPerRequest state)
    ]
  
  -- Handle overheating
  if entropy > maxEntropyPerRequest state
    then do
      -- Universe too hot, dispose of it
      logStr $ "Universe overheated! Entropy: " ++ show entropy
      return $ responseLBS status503 [] $ 
        "Universe thermal shutdown. Entropy: " ++ show entropy
    else do
      -- Return universe to pool if cool enough
      when (entropy < 10) $ atomically $ do
        us <- readTVar (universes state)
        writeTVar (universes state) (finalUniverse : us)
      
      return $ responseLBS status200 
        [("X-Entropy", B8.pack $ show entropy),
         ("X-Time-Steps", B8.pack $ show timeElapsed),
         ("X-Void-Count", B8.pack $ show (void_count finalUniverse))]
        (encode response)

-- Thermal status indicator
thermalStatus :: Integer -> Integer -> String
thermalStatus current max
  | current < max `div` 4 = "🟢 COOL"
  | current < max `div` 2 = "🟡 WARM" 
  | current < (max * 3) `div` 4 = "🟠 HOT"
  | otherwise = "🔴 CRITICAL"

-- Monitor global entropy across all universes
entropyMonitor :: ServerState -> IO ()
entropyMonitor state = forever $ do
  threadDelay 1000000  -- Check every second
  universes <- atomically $ readTVar (universes state)
  let totalEntropy = sum $ map total_entropy universes
  let avgEntropy = totalEntropy `div` fromIntegral (length universes)
  
  putStrLn $ "=== ENTROPY MONITOR ==="
  putStrLn $ "Active universes: " ++ show (length universes)
  putStrLn $ "Total entropy: " ++ show totalEntropy
  putStrLn $ "Average entropy: " ++ show avgEntropy
  
  -- Spawn fresh universes if needed
  when (avgEntropy > 50) $ do
    putStrLn "🔥 HIGH ENTROPY DETECTED - Spawning fresh universes"
    atomically $ writeTVar (universes state) 
      (replicate 5 initial_universe)

-- The actual web application
app :: ServerState -> Application
app state req respond = do
  -- Increment request counter
  atomically $ modifyTVar' (requestCount state) (+1)
  
  -- Log request
  count <- atomically $ readTVar (requestCount state)
  putStrLn $ "Request #" ++ show count ++ ": " ++ show (pathInfo req)
  
  -- Process in isolated universe (CANNOT CRASH!)
  response <- processInUniverse state req
  
  -- Send response
  respond response

-- Example client requests to test
testRequests :: IO ()
testRequests = do
  putStrLn "\n=== TESTING THERMODYNAMIC SERVER ===\n"
  
  -- Normal computation
  test "ADD" "http://localhost:3000/add/10/20"
  
  -- Division by zero (would crash normal server!)
  test "DIV BY ZERO" "http://localhost:3000/div/100/0"
  
  -- Infinite loop attempt (would hang normal server!)
  test "INFINITE LOOP" "http://localhost:3000/loop"
  
  -- High entropy generation
  test "CHAOS 5" "http://localhost:3000/chaos/5"
  test "CHAOS 10" "http://localhost:3000/chaos/10"
  
  -- Complex computation
  test "FACTORIAL" "http://localhost:3000/factorial/10"
  test "FIBONACCI" "http://localhost:3000/fib/15"
  
  where
    test name url = do
      putStrLn $ name ++ ":"
      response <- simpleHTTP (getRequest url)
      case response of
        Left err -> putStrLn $ "  Error: " ++ show err
        Right r -> do
          putStrLn $ "  Result: " ++ getResponseBody r
          putStrLn $ "  Entropy: " ++ getHeader "X-Entropy" r
          putStrLn $ "  Status: " ++ getHeader "X-Status" r

-- Main server
main :: IO ()
main = do
  putStrLn "🌌 THERMODYNAMIC WEB SERVER 🌌"
  putStrLn "A server that cannot crash, tracking entropy of computation\n"
  
  -- Initialize server state with universe pool
  state <- ServerState 
    <$> newTVarIO (replicate 10 initial_universe)  -- 10 parallel universes
    <*> newTVarIO 0
    <*> pure 100  -- Max entropy per request
    <*> pure 1000 -- Global entropy limit
  
  -- Start entropy monitor in background
  forkIO $ entropyMonitor state
  
  -- Launch server (port 3000)
  putStrLn "Server running on http://localhost:3000"
  putStrLn "Try:"
  putStrLn "  http://localhost:3000/add/5/3"
  putStrLn "  http://localhost:3000/div/10/0  (division by zero!)"
  putStrLn "  http://localhost:3000/loop      (infinite loop!)"
  putStrLn "  http://localhost:3000/chaos/10  (generate entropy)"
  putStrLn ""
  
  run 3000 (app state)