module ThermoJSON where

import ThermoLang
import UnravelMonad
import qualified Data.Aeson as A
import qualified Data.Aeson.KeyMap as KM
import qualified Data.Aeson.Key as Key
import qualified Data.Vector as V
import qualified Data.ByteString.Lazy as B
import qualified Data.Map as Map
import Data.Scientific (toBoundedInteger)

-- Convert Aeson Value to Thermodynamic Value
-- This is "Total" conversion.
jsonToUVal :: A.Value -> UVal
jsonToUVal v = case v of
    A.Null -> VList [] -- Represent Null as empty list? Or better, empty object? Let's say Void? 
                       -- No, UVal doesn't have VVoid. 
                       -- Let's treat Null as 0 for now or specific logic.
                       -- Better: Empty List is a safe "Null".
                       
    A.Bool b -> VBool b
    
    A.String t -> VString (show t) -- Convert text to string
    
    A.Number n -> case toBoundedInteger n of
        Just i  -> VInt i
        Nothing -> VInt 0 -- Fallback for floats (prototype limitation)
        
    A.Array a -> VList (map jsonToUVal (V.toList a))
    
    A.Object o -> 
        let list = KM.toList o
            uMap = Map.fromList $ map (\(k, val) -> (Key.toString k, jsonToUVal val)) list
        in VObject uMap

-- The Airlock: Safe IO that returns Unravel
readJson :: FilePath -> Unravel UVal
readJson path = Unravel $ \u ->
    -- This part is tricky. Unravel is pure. 
    -- In a real implementation, we would wrap IO in UnravelT.
    -- For this prototype, we assume the data is already read into the 'compile' environment
    -- OR we use unsafePerformIO (bad practice but ok for prototype).
    -- BETTER: The Main.hs reads the file, converts to UVal, and passes it to 'compile' as env.
    -- So this function is just a helper for Main.
    error "This should be called from IO context"

-- Pure Parser
parseJsonBytes :: B.ByteString -> Either String UVal
parseJsonBytes raw = 
    case A.decode raw of
        Just v  -> Right (jsonToUVal v)
        Nothing -> Left "Invalid JSON"