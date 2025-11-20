//! VoidInfo: The Gateway to Impossibility
//!
//! Based on the Coq specification in UnravelLang.v
//!
//! ## Mathematical Foundation (Gateway Theorem)
//!
//! For any Alpha-like substructure living inside a host, there is a
//! canonical "gateway" predicate that has no witnesses inside the
//! substructure. By uniqueness of impossibility, this gateway IS
//! the impossible predicate (omega_veil).
//!
//! In practice:
//! - Division by zero crosses the gateway
//! - Undefined variables cross the gateway  
//! - Type mismatches cross the gateway
//!
//! All these sources collapse to the same VoidInfo structure because
//! the Gateway theorem proves they're all manifestations of omega_veil.

use std::fmt;

/// Source of impossibility - why the gateway was crossed
///
/// MATHEMATICAL NOTE: These are not different "types" of errors.
/// They are different *witnesses* to the same impossible predicate.
/// The Gateway theorem guarantees they're all equivalent on the
/// substructure (Alpha).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VoidSource {
    /// Division by zero: n / 0
    DivByZero { numerator: i64 },
    
    /// Modulo by zero: n % 0
    ModByZero { numerator: i64 },
    
    /// Undefined variable reference
    UndefinedVar { name: String },
    
    /// Computation exhausted fuel (non-termination boundary)
    OutOfFuel,
    
    /// Type mismatch at runtime
    TypeError { operation: String },
    
    /// Void propagation: combining two impossibilities
    /// 
    /// THEOREM (Impossibility Algebra): Impossible ∧ Impossible = Impossible
    /// The combined entropy is e1 + e2 (proven in FalseThermodynamics.v)
    Propagation {
        parent1: Box<VoidInfo>,
        parent2: Box<VoidInfo>,
    },
}

/// Rich thermodynamic information about void encounters
///
/// MATHEMATICAL FOUNDATION: VoidInfo from Coq (UnravelLang.v)
///
/// ```coq
/// Inductive VoidInfo : Type :=
///   | VInfo : nat ->          (* entropy: how much disorder *)
///             nat ->          (* time: when it happened *)
///             VoidSource ->   (* source: why it failed *)
///             VoidInfo
/// ```
///
/// ## BaseVeil Principle
///
/// THEOREM: All voids have entropy ≥ 1
///
/// This is not a design choice - it's a consequence of the Gateway theorem.
/// Crossing the gateway boundary is an irreversible step that must have
/// thermodynamic cost.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VoidInfo {
    /// Thermodynamic contribution (PROVEN: ≥ 1)
    entropy: u64,
    
    /// When in computational time this occurred
    time_step: u64,
    
    /// Why this impossibility happened
    source: VoidSource,
}

impl VoidInfo {
    /// Create a new void with base entropy
    ///
    /// IMPLEMENTS: BaseVeil principle (entropy ≥ 1)
    pub fn new(time_step: u64, source: VoidSource) -> Self {
        Self {
            entropy: 1,  // BaseVeil: minimum entropy
            time_step,
            source,
        }
    }
    
    /// Create a void with custom entropy
    ///
    /// Used internally for void propagation where entropy > 1
    pub(crate) fn with_entropy(entropy: u64, time_step: u64, source: VoidSource) -> Self {
        debug_assert!(entropy >= 1, "BaseVeil principle violated");
        Self {
            entropy,
            time_step,
            source,
        }
    }
    
    /// Get the thermodynamic contribution
    pub fn entropy(&self) -> u64 {
        self.entropy
    }
    
    /// Get the time step when this void occurred
    pub fn time_step(&self) -> u64 {
        self.time_step
    }
    
    /// Get the source of impossibility
    pub fn source(&self) -> &VoidSource {
        &self.source
    }
    
    /// Combine two voids (impossibility algebra)
    ///
    /// THEOREM (Coq: combine_voids):
    /// ```coq
    /// Definition combine_voids (v1 v2 : VoidInfo) (u : Universe) : VoidInfo :=
    ///   match v1, v2 with
    ///   | VInfo e1 t1 s1, VInfo e2 t2 s2 =>
    ///       VInfo (e1 + e2) u.(time_step) (VoidPropagation v1 v2)
    ///   end.
    /// ```
    ///
    /// PROVEN: Combined entropy = e1 + e2
    pub fn combine(v1: VoidInfo, v2: VoidInfo, current_time: u64) -> Self {
        Self {
            entropy: v1.entropy + v2.entropy,
            time_step: current_time,
            source: VoidSource::Propagation {
                parent1: Box::new(v1),
                parent2: Box::new(v2),
            },
        }
    }
}

impl fmt::Display for VoidSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VoidSource::DivByZero { numerator } => 
                write!(f, "DivByZero({})", numerator),
            VoidSource::ModByZero { numerator } => 
                write!(f, "ModByZero({})", numerator),
            VoidSource::UndefinedVar { name } => 
                write!(f, "UndefinedVar({})", name),
            VoidSource::OutOfFuel => 
                write!(f, "OutOfFuel"),
            VoidSource::TypeError { operation } => 
                write!(f, "TypeError({})", operation),
            VoidSource::Propagation { parent1, parent2 } => 
                write!(f, "Propagation[e={} + e={}]", parent1.entropy, parent2.entropy),
        }
    }
}

impl fmt::Display for VoidInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "VoidInfo {{ entropy: {}, time: {}, source: {} }}",
            self.entropy, self.time_step, self.source
        )
    }
}
