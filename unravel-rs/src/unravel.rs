//! Unravel: The Monad That Respects Physics
//!
//! Based on the Coq specification and Haskell implementation
//!
//! ## Mathematical Foundation
//!
//! The Unravel monad threads Universe state through computations,
//! tracking thermodynamic cost of gateway crossings.
//!
//! ## Monad Laws (proven in Coq)
//!
//! 1. Left identity: `pure(x).bind(f) ≡ f(x)`
//! 2. Right identity: `m.bind(pure) ≡ m`
//! 3. Associativity: `m.bind(f).bind(g) ≡ m.bind(|x| f(x).bind(g))`
//!
//! ## Applicative Semantics
//!
//! Unlike typical Either monads, Applicative `<*>` evaluates BOTH branches:
//! - If both fail: entropies add (void propagation)
//! - If one fails: that void is returned
//! - If both succeed: result succeeds
//!
//! This models physical reality: both branches of reality are explored,
//! and their thermodynamic costs accumulate.

use crate::{Universe, VoidInfo};
use std::fmt;

/// Result of an Unravel computation
///
/// MATHEMATICAL NOTE: This is NOT a standard Result type.
/// It's grounded in the Gateway theorem - Valid means we stayed
/// within the substructure, Void means we crossed the gateway.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UResult<T> {
    /// Computation stayed within bounds (Alpha)
    Valid(T),
    
    /// Computation crossed the gateway (touched omega_veil)
    Void(VoidInfo),
}

impl<T> UResult<T> {
    /// Check if result is valid
    pub fn is_valid(&self) -> bool {
        matches!(self, UResult::Valid(_))
    }
    
    /// Check if result is void
    pub fn is_void(&self) -> bool {
        matches!(self, UResult::Void(_))
    }
    
    /// Get the valid value if present
    pub fn as_valid(&self) -> Option<&T> {
        match self {
            UResult::Valid(v) => Some(v),
            UResult::Void(_) => None,
        }
    }
    
    /// Get the void info if present
    pub fn as_void(&self) -> Option<&VoidInfo> {
        match self {
            UResult::Valid(_) => None,
            UResult::Void(info) => Some(info),
        }
    }
    
    /// Map over valid values
    pub fn map<U, F>(self, f: F) -> UResult<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            UResult::Valid(v) => UResult::Valid(f(v)),
            UResult::Void(info) => UResult::Void(info),
        }
    }
}

/// The Unravel monad: State (Universe) + Result (Either)
///
/// IMPLEMENTS: Unravel from Haskell (UnravelMonad.hs)
/// ```haskell
/// newtype Unravel a = Unravel {
///     runUnravel :: Universe -> (UResult a, Universe)
/// }
/// ```
///
/// This is a State monad carrying Universe, combined with Either
/// semantics for short-circuiting on void.
pub struct Unravel<T> {
    run_fn: Box<dyn FnOnce(Universe) -> (UResult<T>, Universe)>,
}

impl<T: 'static> Unravel<T> {
    /// Create an Unravel computation from a function
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce(Universe) -> (UResult<T>, Universe) + 'static,
    {
        Self { run_fn: Box::new(f) }
    }
    
    /// Run the computation from initial universe
    ///
    /// IMPLEMENTS: run from Haskell
    /// ```haskell
    /// run :: Unravel a -> (UResult a, Universe)
    /// run prog = runUnravel prog bigBang
    /// ```
    pub fn run(self) -> (UResult<T>, Universe) {
        self.run_with(Universe::new())
    }
    
    /// Run the computation from a specific universe state
    pub fn run_with(self, universe: Universe) -> (UResult<T>, Universe) {
        (self.run_fn)(universe)
    }
    
    /// Pure (return): Lift a value into the monad
    ///
    /// IMPLEMENTS: pure from Haskell Applicative
    /// ```haskell
    /// pure x = Unravel $ \u -> (Valid x, u)
    /// ```
    ///
    /// No gateway crossing, no entropy change, no time advance.
    pub fn pure(value: T) -> Self {
        Self::new(move |u| (UResult::Valid(value), u))
    }
    
    /// Crumble: Create a void (cross the gateway)
    ///
    /// IMPLEMENTS: crumble from Haskell
    /// ```haskell
    /// crumble :: VoidSource -> Unravel a
    /// crumble src = Unravel $ \u ->
    ///     let info = VoidInfo 1 src
    ///         u' = u { totalEntropy = totalEntropy u + 1
    ///                , voidCount = voidCount u + 1 }
    ///     in (Invalid info, u')
    /// ```
    pub fn crumble(info: VoidInfo) -> Self {
        Self::new(move |u| {
            let u_evolved = u.evolve(&info);
            (UResult::Void(info), u_evolved)
        })
    }
    
    /// Monadic bind (>>=)
    ///
    /// IMPLEMENTS: (>>=) from Haskell Monad
    /// ```haskell
    /// (Unravel x) >>= f = Unravel $ \u ->
    ///     let (res, u') = x u
    ///         uTimed = u' { timeStep = timeStep u' + 1 }
    ///     in case res of
    ///         Valid val -> runUnravel (f val) uTimed
    ///         Invalid i -> (Invalid i, uTimed)
    /// ```
    ///
    /// Time advances even on void (the attempt has computational cost).
    pub fn bind<U: 'static, F>(self, f: F) -> Unravel<U>
    where
        F: FnOnce(T) -> Unravel<U> + 'static,
    {
        Unravel::new(move |u| {
            let (result, u_prime) = (self.run_fn)(u);
            let u_timed = u_prime.tick();
            
            match result {
                UResult::Valid(val) => f(val).run_with(u_timed),
                UResult::Void(info) => (UResult::Void(info), u_timed),
            }
        })
    }
    
    /// Map over the value (functor)
    pub fn map<U: 'static, F>(self, f: F) -> Unravel<U>
    where
        F: FnOnce(T) -> U + 'static,
    {
        Unravel::new(move |u| {
            let (result, u_prime) = (self.run_fn)(u);
            (result.map(f), u_prime)
        })
    }
    
    /// Recover from void with default value
    ///
    /// IMPLEMENTS: recover from Haskell
    /// ```haskell
    /// recover :: Unravel a -> a -> Unravel a
    /// recover (Unravel op) defaultVal = Unravel $ \u ->
    ///     case op u of
    ///         (Valid x, u') -> (Valid x, u')
    ///         (Invalid _, u') -> (Valid defaultVal, u')
    /// ```
    ///
    /// NOTE: The universe state is preserved, including entropy.
    /// Recovery doesn't erase the thermodynamic cost of failure.
    pub fn recover(self, default: T) -> Self
    {
        Unravel::new(move |u| {
            let (result, u_prime) = (self.run_fn)(u);
            match result {
                UResult::Valid(_) => (result, u_prime),
                UResult::Void(_) => (UResult::Valid(default), u_prime),
            }
        })
    }
    
    /// Combine two computations (applicative style)
    ///
    /// IMPLEMENTS: (<*>) from Haskell Applicative with BOTH branches evaluated
    /// ```haskell
    /// (Unravel f) <*> (Unravel x) = Unravel $ \u ->
    ///     let (resF, u') = f u
    ///         (resX, u'') = x u'
    ///         uTimed = u'' { timeStep = timeStep u'' + 1 }
    ///     in case (resF, resX) of
    ///         (Valid func, Valid val) -> (Valid (func val), uTimed)
    ///         (Invalid i, Valid _) -> (Invalid i, uTimed)
    ///         (Valid _, Invalid i) -> (Invalid i, uTimed)
    ///         (Invalid i1, Invalid i2) ->
    ///             let newVoid = combineVoids i1 i2
    ///                 uFinal = uTimed { totalEntropy = totalEntropy uTimed + entropy newVoid
    ///                                 , voidCount = voidCount uTimed + 1 }
    ///             in (Invalid newVoid, uFinal)
    /// ```
    ///
    /// CRITICAL: Both branches are evaluated! This models physical reality.
    pub fn combine_with<U: 'static>(self, other: Unravel<U>) -> Unravel<(T, U)>
    {
        Unravel::new(move |u| {
            // Evaluate first
            let (res1, u_prime) = (self.run_fn)(u);
            // Evaluate second
            let (res2, u_double_prime) = (other.run_fn)(u_prime);
            // Time advances
            let u_timed = u_double_prime.tick();
            
            match (res1, res2) {
                (UResult::Valid(v1), UResult::Valid(v2)) => {
                    (UResult::Valid((v1, v2)), u_timed)
                }
                (UResult::Void(info), UResult::Valid(_)) => {
                    (UResult::Void(info), u_timed)
                }
                (UResult::Valid(_), UResult::Void(info)) => {
                    (UResult::Void(info), u_timed)
                }
                (UResult::Void(i1), UResult::Void(i2)) => {
                    // Void propagation: entropies add
                    let combined = VoidInfo::combine(i1, i2, u_timed.time_step());
                    let u_final = u_timed.evolve(&combined);
                    (UResult::Void(combined), u_final)
                }
            }
        })
    }
}

impl<T: fmt::Debug> fmt::Debug for Unravel<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Unravel(<closure>)")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VoidSource;
    
    #[test]
    fn test_pure() {
        let m = Unravel::pure(42);
        let (result, u) = m.run();
        
        assert!(matches!(result, UResult::Valid(42)));
        assert!(u.is_initial());  // No side effects
    }
    
    #[test]
    fn test_crumble() {
        let void = VoidInfo::new(0, VoidSource::DivByZero { numerator: 10 });
        let m = Unravel::<i32>::crumble(void.clone());
        let (result, u) = m.run();
        
        assert!(result.is_void());
        assert_eq!(u.total_entropy(), 1);  // BaseVeil
        assert_eq!(u.void_count(), 1);
    }
    
    #[test]
    fn test_bind_pure() {
        let m = Unravel::pure(10)
            .bind(|x| Unravel::pure(x * 2));
        
        let (result, _u) = m.run();
        assert_eq!(result.as_valid(), Some(&20));
    }
    
    #[test]
    fn test_bind_void_short_circuits() {
        let void = VoidInfo::new(0, VoidSource::DivByZero { numerator: 10 });
        let m = Unravel::<i32>::crumble(void)
            .bind(|x| Unravel::pure(x * 2));
        
        let (result, u) = m.run();
        assert!(result.is_void());
        assert_eq!(u.total_entropy(), 1);
    }
    
    #[test]
    fn test_recover() {
        let void = VoidInfo::new(0, VoidSource::DivByZero { numerator: 10 });
        let m = Unravel::<i32>::crumble(void)
            .recover(42);
        
        let (result, u) = m.run();
        assert_eq!(result.as_valid(), Some(&42));
        assert_eq!(u.total_entropy(), 1);  // Entropy preserved!
    }
}
