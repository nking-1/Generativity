module Control.Monad.Unravel.SafeIO where

import Control.Monad.Unravel
import Data.Unravel.Universe
import Control.Monad.IO.Class
import Control.Exception (try, IOException, SomeException, displayException)

-- | Safely execute an IO action.
-- If it throws ANY exception, it crumbles into Entropy.
-- Because 'crumble' returns 'Invalid', the result 'a' is technically never returned.
-- This must be used inside a 'shield' to be useful, or propagate the error.
safeIO :: (MonadIO m) => IO a -> UnravelT m a
safeIO action = do
    -- We perform the IO in the base monad, capturing exceptions
    result <- liftIO (try action :: IO (Either SomeException a))
    case result of
        Right val -> return val
        Left err  -> crumble (IOException (displayException err))

-- | A safe wrapper for Division to prove we handle pure exceptions too
safeDiv :: (Monad m) => Int -> Int -> UnravelT m Int
safeDiv _ 0 = crumble DivByZero
safeDiv n d = return (n `div` d)

-- | Checkpoint: Returns the current Holographic Signature
checkpoint :: Monad m => UnravelT m Integer
checkpoint = do
    u <- getUniverse
    return (boundaryValue u)