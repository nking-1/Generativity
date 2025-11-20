//! Universe: Thermodynamic State of Computation
//!
//! Based on the Coq specification in UnravelLang.v
//!
//! ## Mathematical Foundation
//!
//! ```coq
//! Record Universe := {
//!   total_entropy : nat;
//!   time_step : nat;
//!   void_count : nat
//! }.
//! ```
//!
//! ## Conservation Laws (Noether's Theorem)
//!
//! THEOREM (entropy_second_law): Entropy never decreases
//! THEOREM (time_arrow): Time always advances
//! THEOREM (void_accumulation): Void count is monotonic
//!
//! These are not design choices - they're consequences of the
//! mathematical structure. Noether's theorem proves that
//! symmetries preserving omega_veil correspond to conservation laws.

use crate::VoidInfo;
use std::fmt;

/// The universe state during computation
///
/// INVARIANTS (proven in Coq):
/// 1. Entropy never decreases (Second Law of Thermodynamics)
/// 2. Time always advances (Arrow of Time)
/// 3. Void count is monotonic (void accumulation)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Universe {
    /// Total accumulated entropy
    /// PROVEN: Can only increase (entropy_second_law)
    total_entropy: u64,
    
    /// Current computational time step
    /// PROVEN: Can only increase (time_arrow)
    time_step: u64,
    
    /// Number of void encounters
    /// PROVEN: Can only increase (void_accumulation)
    void_count: u64,
}

impl Universe {
    /// Create the initial universe (Big Bang)
    ///
    /// IMPLEMENTS: initial_universe from Coq
    /// ```coq
    /// Definition initial_universe : Universe := {|
    ///   total_entropy := 0;
    ///   time_step := 0;
    ///   void_count := 0
    /// |}.
    /// ```
    pub fn new() -> Self {
        Self {
            total_entropy: 0,
            time_step: 0,
            void_count: 0,
        }
    }
    
    /// Create universe from constituent parts
    ///
    /// Used internally for parallel universe merging
    pub(crate) fn from_parts(total_entropy: u64, time_step: u64, void_count: u64) -> Self {
        Self {
            total_entropy,
            time_step,
            void_count,
        }
    }
    
    /// Get total accumulated entropy
    pub fn total_entropy(&self) -> u64 {
        self.total_entropy
    }
    
    /// Get current time step
    pub fn time_step(&self) -> u64 {
        self.time_step
    }
    
    /// Get number of void encounters
    pub fn void_count(&self) -> u64 {
        self.void_count
    }
    
    /// Evolve universe when encountering void
    ///
    /// IMPLEMENTS: evolve_universe from Coq
    /// ```coq
    /// Definition evolve_universe (u : Universe) (info : VoidInfo) : Universe :=
    ///   match info with
    ///   | VInfo entropy _ _ => {|
    ///       total_entropy := u.(total_entropy) + entropy;
    ///       time_step := S u.(time_step);
    ///       void_count := S u.(void_count)
    ///     |}
    ///   end.
    /// ```
    ///
    /// PROVEN LAWS:
    /// - total_entropy' ≥ total_entropy (entropy_second_law)
    /// - time_step' = time_step + 1 (time_arrow)
    /// - void_count' = void_count + 1 (void_accumulation)
    pub fn evolve(&self, info: &VoidInfo) -> Self {
        Self {
            total_entropy: self.total_entropy + info.entropy(),
            time_step: self.time_step + 1,
            void_count: self.void_count + 1,
        }
    }
    
    /// Advance time without entropy change
    ///
    /// Used for pure computations (no gateway crossing)
    pub fn tick(&self) -> Self {
        Self {
            total_entropy: self.total_entropy,
            time_step: self.time_step + 1,
            void_count: self.void_count,
        }
    }
    
    /// Check if universe is still in initial state
    pub fn is_initial(&self) -> bool {
        self.total_entropy == 0 && self.time_step == 0 && self.void_count == 0
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Universe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Universe {{ entropy: {}, time: {}, voids: {} }}",
            self.total_entropy, self.time_step, self.void_count
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VoidSource;
    
    #[test]
    fn test_initial_universe() {
        let u = Universe::new();
        assert_eq!(u.total_entropy(), 0);
        assert_eq!(u.time_step(), 0);
        assert_eq!(u.void_count(), 0);
        assert!(u.is_initial());
    }
    
    #[test]
    fn test_entropy_second_law() {
        let u = Universe::new();
        let void = VoidInfo::new(0, VoidSource::DivByZero { numerator: 10 });
        let u2 = u.evolve(&void);
        
        // Entropy never decreases
        assert!(u2.total_entropy() >= u.total_entropy());
        assert_eq!(u2.total_entropy(), 1);  // BaseVeil
    }
    
    #[test]
    fn test_time_arrow() {
        let u = Universe::new();
        let void = VoidInfo::new(0, VoidSource::DivByZero { numerator: 10 });
        let u2 = u.evolve(&void);
        
        // Time always advances
        assert!(u2.time_step() > u.time_step());
        assert_eq!(u2.time_step(), 1);
    }
    
    #[test]
    fn test_void_accumulation() {
        let u = Universe::new();
        let void = VoidInfo::new(0, VoidSource::DivByZero { numerator: 10 });
        let u2 = u.evolve(&void);
        
        // Void count is monotonic
        assert!(u2.void_count() >= u.void_count());
        assert_eq!(u2.void_count(), 1);
    }
}
