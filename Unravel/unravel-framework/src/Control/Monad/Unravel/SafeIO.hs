{-# LANGUAGE ScopedTypeVariables #-}

module Control.Monad.Unravel.SafeIO where

import Control.Monad.Unravel
import Data.Unravel.Universe
import Control.Monad.IO.Class
import Control.Exception (try, SomeException, displayException)

-- | Safely execute an IO action.
-- If it throws ANY exception, it crumbles into Entropy.
safeIO :: forall m a. (MonadIO m) => IO a -> UnravelT m a
safeIO action = do
    -- We catch SomeException. We don't constrain 'a' explicitly in the expression,
    -- we let GHC infer it from the return type.
    result <- liftIO (try action)
    case result of
        Right val -> return val
        Left (err :: SomeException) -> crumble (IOException (displayException err))

-- | A safe wrapper for Division to prove we handle pure exceptions too
safeDiv :: (Monad m) => Int -> Int -> UnravelT m Int
safeDiv _ 0 = crumble DivByZero
safeDiv n d = return (n `div` d)

-- | Checkpoint: Returns the current Holographic Signature
checkpoint :: Monad m => UnravelT m Integer
checkpoint = do
    u <- getUniverse
    return (boundaryValue u)