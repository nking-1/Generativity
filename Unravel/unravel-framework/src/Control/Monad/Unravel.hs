{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Monad.Unravel where

import Data.Unravel.Universe
import Control.Monad.State.Strict
import Control.Monad.IO.Class
import Control.Monad.Catch (MonadThrow, MonadCatch, catch, SomeException, displayException)
import qualified Data.List as List

-- The Result Type (Internal)
data UResult a 
    = Valid a 
    | Invalid ParadoxPath -- Carries the history of the crash
    deriving (Show, Eq, Functor)

-- The Transformer: StateT + Custom Error Logic
newtype UnravelT m a = UnravelT { 
    runUnravelT_ :: StateT Universe m (UResult a) 
}

-- Type Alias for pure computations
type Unravel = UnravelT Identity

-- ==========================================
-- 1. INSTANCES (The Magic)
-- ==========================================

instance Monad m => Functor (UnravelT m) where
    fmap f x = UnravelT $ do
        res <- runUnravelT_ x
        case res of
            Valid a -> return (Valid (f a))
            Invalid p -> return (Invalid p)

instance Monad m => Applicative (UnravelT m) where
    pure x = UnravelT $ return (Valid x)
    
    -- The "Entanglement" Operator
    (UnravelT mf) <*> (UnravelT mx) = UnravelT $ do
        fRes <- mf
        xRes <- mx
        -- Tick the clock for every step
        modify (\u -> u { timeStep = timeStep u + 1 })
        
        case (fRes, xRes) of
            (Valid f, Valid x) -> return (Valid (f x))
            (Invalid p, Valid _) -> return (Invalid p)
            (Valid _, Invalid p) -> return (Invalid p)
            
            -- COLLISION: Merge histories (Structural Entropy)
            (Invalid p1, Invalid p2) -> do
                let newPath = Compose p1 p2
                updateUniverseWith newPath
                return (Invalid newPath)

instance Monad m => Monad (UnravelT m) where
    return = pure
    
    -- The "Timeline" Operator
    (UnravelT mx) >>= f = UnravelT $ do
        res <- mx
        -- Tick clock
        modify (\u -> u { timeStep = timeStep u + 1 })
        
        case res of
            Valid x -> runUnravelT_ (f x)
            
            -- EVOLUTION: Propagate error in time (Time Entropy)
            Invalid p -> do
                let newPath = SelfContradict p
                -- Note: We don't re-add entropy here to avoid double counting in loops,
                -- but we DO evolve the universe state to record the passage of time.
                -- For v1.0, let's update the boundary to show persistence.
                updateUniverseWith newPath
                return (Invalid newPath)

instance MonadIO m => MonadIO (UnravelT m) where
    liftIO io = UnravelT $ do
        -- Optimistic execution. If it crashes, the outer runner handles it.
        -- But inside UnravelT, we assume valid lift. 
        -- Use 'safeIO' for dangerous things.
        res <- liftIO io
        return (Valid res)

-- ==========================================
-- 2. HELPER FUNCTIONS
-- ==========================================

updateUniverseWith :: Monad m => ParadoxPath -> StateT Universe m ()
updateUniverseWith path = do
    u <- get
    let (dS, dT) = rankOf path
    let tokens = flattenPath path
    let bVal   = compress tokens
    let bLen   = length tokens
    let (finalVal, finalLen) = appendHologram (boundaryValue u) (boundaryLength u) bVal bLen
    
    put $ u { structEntropy = structEntropy u + dS
            , timeEntropy   = timeEntropy u + dT
            , voidCount     = voidCount u + 1
            , boundaryValue = finalVal
            , boundaryLength = finalLen
            }

-- ==========================================
-- 3. THE PRIMITIVES (API)
-- ==========================================

-- The Singularity Generator
crumble :: Monad m => VoidSource -> UnravelT m a
crumble src = UnravelT $ do
    let path = BaseVeil src
    updateUniverseWith path
    return (Invalid path)

-- The Observer (Shield)
-- Converts Invalid state back to Valid state using a default
shield :: Monad m => UnravelT m a -> a -> UnravelT m a
shield action def = UnravelT $ do
    res <- runUnravelT_ action
    case res of
        Valid a -> return (Valid a)
        Invalid p -> do
            -- We keep the universe changes (entropy), but return Valid
            return (Valid def)

-- Work (Mass)
work :: Monad m => Int -> UnravelT m ()
work w = UnravelT $ do
    modify (\u -> u { mass = mass u + w })
    return (Valid ())

-- Introspection
getUniverse :: Monad m => UnravelT m Universe
getUniverse = UnravelT $ Valid <$> get

-- Execution Runner
runUnravelT :: Monad m => UnravelT m a -> m (UResult a, Universe)
runUnravelT action = runStateT (runUnravelT_ action) emptyUniverse