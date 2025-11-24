//! # Unravel: Thermodynamic Computation
//!
//! A monad implementation where error handling respects physical laws.
//!
//! ## Core Concepts
//!
//! - **VoidInfo**: The omega_veil - the unique impossible predicate that all errors collapse to
//! - **Universe**: Thermodynamic state tracking entropy, time, and void encounters
//! - **Unravel<T>**: A monad that threads universe state through computations
//!
//! ## Mathematical Foundation
//!
//! Based on the Gateway theorem from DAO/Rocq theory:
//! - All impossible predicates are equivalent (omega_veil uniqueness)
//! - Crossing the gateway has thermodynamic cost (entropy ≥ 1)
//! - Conservation laws emerge from symmetries (Noether's theorem)
//!
//! ## Example
//!
//! ```rust
//! use unravel::*;
//!
//! let result = Unravel::pure(10)
//!     .bind(|x| divide(x, 0))  // Division by zero
//!     .recover(42);             // Recover with default
//!
//! let (value, universe) = result.run();
//! assert_eq!(value.as_valid(), Some(&42));
//! assert!(universe.total_entropy() >= 1);  // BaseVeil principle
//! ```

mod void_info;
mod universe;
mod unravel;
mod ops;
mod compute;
mod interop;

pub use void_info::{VoidInfo, VoidSource};
pub use universe::Universe;
pub use unravel::{Unravel, UResult};
pub use ops::{divide, add, multiply, divide_zc};
pub use compute::{Compute, Pure, Crumble, Bind, Map, Recover, CombineWith, ParallelCombine, ParallelMode};
pub use interop::{from_result, ResultExt};

// Re-export commonly used items
pub mod prelude {
    pub use crate::{Unravel, UResult, VoidInfo, VoidSource, Universe};
    pub use crate::ops::*;
    pub use crate::compute::{Compute, Pure, Bind, ParallelMode, ParallelCombine};
    pub use crate::interop::{from_result, ResultExt};
}
