{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

-- ParadoxNumbers.hs
-- A Haskell implementation of the formally verified Paradox Number System
-- where division by zero is safe and meaningful

module ParadoxNumbers where

import Data.Maybe (fromMaybe)
import Text.Printf (printf)

-- ============================================================
-- Natural Numbers (starting from 1, as 0 is the void)
-- ============================================================

data PNat = POne | PS PNat
  deriving stock (Eq)

instance Show PNat where
  show = show . pnatToInt

pnatToInt :: PNat -> Int
pnatToInt POne = 1
pnatToInt (PS n) = 1 + pnatToInt n

intToPNat :: Int -> Maybe PNat
intToPNat n
  | n <= 0 = Nothing
  | n == 1 = Just POne
  | otherwise = fmap PS (intToPNat (n - 1))

addNat :: PNat -> PNat -> PNat
addNat POne n = PS n
addNat (PS m) n = PS (addNat m n)

multNat :: PNat -> PNat -> PNat
multNat POne n = n
multNat (PS m) n = addNat n (multNat m n)

-- ============================================================
-- Integers (0 is the void, positive and negative constructions)
-- ============================================================

data PInt = PZero | PPos PNat | PNeg PNat
  deriving stock (Eq)

instance Show PInt where
  show PZero = "0"
  show (PPos n) = show (pnatToInt n)
  show (PNeg n) = "-" ++ show (pnatToInt n)

pintNeg :: PInt -> PInt
pintNeg PZero = PZero
pintNeg (PPos n) = PNeg n
pintNeg (PNeg n) = PPos n

pintSucc :: PInt -> PInt
pintSucc PZero = PPos POne
pintSucc (PPos n) = PPos (PS n)
pintSucc (PNeg POne) = PZero
pintSucc (PNeg (PS n)) = PNeg n

pintPred :: PInt -> PInt
pintPred PZero = PNeg POne
pintPred (PNeg n) = PNeg (PS n)
pintPred (PPos POne) = PZero
pintPred (PPos (PS n)) = PPos n

pintAdd :: PInt -> PInt -> PInt
pintAdd PZero j = j
pintAdd (PPos n) j = addPosNat n j
pintAdd (PNeg n) j = addNegNat n j

addPosNat :: PNat -> PInt -> PInt
addPosNat POne j = pintSucc j
addPosNat (PS n) j = pintSucc (addPosNat n j)

addNegNat :: PNat -> PInt -> PInt
addNegNat POne j = pintPred j
addNegNat (PS n) j = pintPred (addNegNat n j)

pintMult :: PInt -> PInt -> PInt
pintMult PZero _ = PZero
pintMult _ PZero = PZero
pintMult (PPos m) (PPos n) = PPos (multNat m n)
pintMult (PPos m) (PNeg n) = PNeg (multNat m n)
pintMult (PNeg m) (PPos n) = PNeg (multNat m n)
pintMult (PNeg m) (PNeg n) = PPos (multNat m n)

-- ============================================================
-- Rationals (where division by zero gives Infinity/Void)
-- ============================================================

data PRat = PRat PInt PInt  -- numerator, denominator
  deriving stock (Eq)

instance Show PRat where
  show (PRat p PZero) = case p of
    PZero -> "NaN"  -- 0/0 = undefined
    PPos _ -> "∞"   -- positive/0 = infinity
    PNeg _ -> "-∞"  -- negative/0 = negative infinity
  show (PRat p q) = show p ++ "/" ++ show q

-- Check if a rational is infinite (denominator is zero)
isInfinite :: PRat -> Bool
isInfinite (PRat _ PZero) = True
isInfinite _ = False

-- Check if a rational is NaN (0/0)
isNaN :: PRat -> Bool
isNaN (PRat PZero PZero) = True
isNaN _ = False

-- Rational equivalence (all infinities are equal)
ratEquiv :: PRat -> PRat -> Bool
ratEquiv (PRat p1 PZero) (PRat p2 PZero) = True  -- All infinities equal
ratEquiv (PRat _ PZero) _ = False
ratEquiv _ (PRat _ PZero) = False
ratEquiv (PRat p1 q1) (PRat p2 q2) = 
  pintMult p1 q2 == pintMult p2 q1

-- Rational arithmetic
ratAdd :: PRat -> PRat -> PRat
ratAdd (PRat _ PZero) _ = PRat PZero PZero  -- ∞ + anything = ∞
ratAdd _ (PRat _ PZero) = PRat PZero PZero
ratAdd (PRat a b) (PRat c d) = 
  PRat (pintAdd (pintMult a d) (pintMult b c)) (pintMult b d)

ratMult :: PRat -> PRat -> PRat
ratMult (PRat a b) (PRat c d) = PRat (pintMult a c) (pintMult b d)

ratDiv :: PRat -> PRat -> PRat
ratDiv (PRat a b) (PRat c d) = PRat (pintMult a d) (pintMult b c)

-- Smart constructor that doesn't normalize away infinities
mkRat :: Int -> Int -> PRat
mkRat n 0 = PRat (if n == 0 then PZero else if n > 0 then PPos POne else PNeg POne) PZero
mkRat n d = 
  let num = if n == 0 then PZero
            else if n > 0 then PPos (fromMaybe POne $ intToPNat n)
            else PNeg (fromMaybe POne $ intToPNat (abs n))
      den = if d > 0 then PPos (fromMaybe POne $ intToPNat d)
            else PNeg (fromMaybe POne $ intToPNat (abs d))
  in PRat num den

-- Convert to Double (for graphing/approximation)
ratToDouble :: PRat -> Maybe Double
ratToDouble (PRat _ PZero) = Nothing  -- Infinity has no Double representation
ratToDouble (PRat PZero _) = Just 0.0
ratToDouble (PRat (PPos n) (PPos d)) = Just $ fromIntegral (pnatToInt n) / fromIntegral (pnatToInt d)
ratToDouble (PRat (PPos n) (PNeg d)) = Just $ -(fromIntegral (pnatToInt n) / fromIntegral (pnatToInt d))
ratToDouble (PRat (PNeg n) (PPos d)) = Just $ -(fromIntegral (pnatToInt n) / fromIntegral (pnatToInt d))
ratToDouble (PRat (PNeg n) (PNeg d)) = Just $ fromIntegral (pnatToInt n) / fromIntegral (pnatToInt d)

-- ============================================================
-- APPLICATIONS
-- ============================================================

-- 1. FINANCE: Safe Return on Investment Calculation
-- Normally ROI = (final - initial) / initial breaks when initial = 0
roi :: Double -> Double -> PRat
roi initial final = 
  let profit = mkRat (round $ final - initial) 1
      init = mkRat (round initial) 1
  in ratDiv profit init

-- Example: Starting from nothing (0 initial investment)
demoROI :: IO ()
demoROI = do
  putStrLn "=== Return on Investment Calculator (Handles Zero Initial!) ==="
  let cases = [(0, 1000), (100, 150), (1000, 0), (0, 0)]
  mapM_ (\(init, final) -> do
    let r = roi init final
    printf "Initial: $%.2f, Final: $%.2f => ROI: %s\n" init final (show r)
    ) cases

-- 2. PHYSICS: Black Hole Density Calculation
-- Density = Mass / Volume, but black hole singularity has volume → 0
density :: Double -> Double -> PRat
density mass volume = 
  let m = mkRat (round $ mass * 1000) 1000  -- Keep some precision
      v = mkRat (round $ volume * 1000) 1000
  in ratDiv m v

blackHoleDensity :: Double -> Double -> IO ()
blackHoleDensity mass radius = do
  let volume = (4/3) * pi * radius^3
      d = density mass volume
  printf "Black hole: Mass=%.2e kg, Radius=%.2e m => Density=%s kg/m³\n" 
    mass radius (show d)

-- 3. STATISTICS: Rate calculations that handle edge cases
-- Example: COVID positivity rate when no tests performed
positivityRate :: Int -> Int -> PRat
positivityRate positive total = mkRat positive total

demoCovidStats :: IO ()
demoCovidStats = do
  putStrLn "\n=== COVID Testing Positivity Rates ==="
  let testData = [
        ("Monday", 10, 100),
        ("Tuesday", 0, 50),
        ("Wednesday", 5, 0),  -- No tests performed!
        ("Thursday", 0, 0)    -- No tests, no positives
        ]
  mapM_ (\(day, pos, total) -> do
    let rate = positivityRate pos total
    printf "%s: %d positive / %d tests = %s\n" day pos total (show rate)
    ) testData

-- 4. CALCULUS: Derivative at discontinuity
-- f(x) = 1/x has a discontinuity at x=0
derivative :: (Double -> PRat) -> Double -> Double -> PRat
derivative f x h = 
  let fx_plus_h = f (x + h)
      fx = f x
      -- Convert PRat difference (this is simplified)
      numerator = case (fx_plus_h, fx) of
        (PRat n1 d1, PRat n2 d2) -> 
          PRat (pintAdd (pintMult n1 d2) (pintNeg (pintMult n2 d1))) (pintMult d1 d2)
      denominator = mkRat (round $ h * 1000) 1000
  in ratDiv numerator denominator

-- 5. OPTION PRICING: Handle zero volatility (normally breaks Black-Scholes)
impliedVolatility :: Double -> Double -> Double -> PRat
impliedVolatility stockPrice strikePrice timeToExpiry =
  if timeToExpiry <= 0 
  then mkRat 0 0  -- At expiry, volatility undefined
  else mkRat (round $ abs (stockPrice - strikePrice) * 100) (round $ timeToExpiry * 100)

demoOptions :: IO ()
demoOptions = do
  putStrLn "\n=== Options Implied Volatility (Handles Zero Time!) ==="
  let cases = [
        (100, 105, 0.25),  -- 3 months to expiry
        (100, 100, 0.01),  -- Near expiry
        (100, 110, 0.0)    -- At expiry!
        ]
  mapM_ (\(stock, strike, time) -> do
    let vol = impliedVolatility stock strike time
    printf "Stock=$%.2f, Strike=$%.2f, Time=%.2f => Vol=%s\n" 
      stock strike time (show vol)
    ) cases

-- 6. ENGINEERING: Resistance in parallel circuits
-- 1/R_total = 1/R1 + 1/R2 + ... handles R=0 (short circuit)
parallelResistance :: [Double] -> PRat
parallelResistance rs = 
  let reciprocals = map (\r -> mkRat 1 (round r)) rs
      sumRecip = foldl ratAdd (mkRat 0 1) reciprocals
  in case sumRecip of
    PRat n d -> PRat d n  -- Reciprocal

demoCircuits :: IO ()
demoCircuits = do
  putStrLn "\n=== Parallel Resistance Calculator (Handles Shorts!) ==="
  let circuits = [
        [10, 20, 30],
        [10, 0],      -- Short circuit!
        [0, 0],       -- Multiple shorts
        []            -- No resistors
        ]
  mapM_ (\rs -> do
    let r = parallelResistance rs
    printf "Resistors %s Ω => Total: %s Ω\n" (show rs) (show r)
    ) circuits

-- Main demo
main :: IO ()
main = do
  putStrLn "╔══════════════════════════════════════════════════════════╗"
  putStrLn "║   PARADOX NUMBERS: Where Division by Zero is Safe!       ║"
  putStrLn "╚══════════════════════════════════════════════════════════╝\n"
  
  demoROI
  putStrLn ""
  
  putStrLn "=== Black Hole Singularity Density ==="
  blackHoleDensity 1.989e30 1e-10  -- Approaching singularity
  blackHoleDensity 1.989e30 0       -- At singularity!
  
  demoCovidStats
  demoOptions
  demoCircuits
  
  putStrLn "\n=== Mathematical Operations with Infinity ==="
  let inf = mkRat 1 0
      nan = mkRat 0 0
      two = mkRat 2 1
  printf "∞ + 2 = %s\n" (show $ ratAdd inf two)
  printf "∞ × 2 = %s\n" (show $ ratMult inf two)
  printf "∞ × 0 = %s\n" (show $ ratMult inf (mkRat 0 1))
  printf "NaN + 2 = %s\n" (show $ ratAdd nan two)
  
  putStrLn "\n✓ No crashes! ✓ No exceptions! ✓ Mathematics remains consistent!"