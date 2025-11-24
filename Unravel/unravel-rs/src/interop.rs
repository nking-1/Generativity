//! Interoperability with standard Rust error types
//!
//! This module provides conversions between `std::result::Result`
//! and the Unravel monad, allowing seamless integration with
//! existing Rust code.

use crate::{UResult, VoidInfo, VoidSource, Universe};
use crate::compute::{Pure, Crumble, Compute};
use std::fmt;

/// Extend VoidSource to handle external errors
impl VoidSource {
    /// Create a void source from an external error
    pub fn from_external<E: fmt::Display>(error: E) -> Self {
        VoidSource::TypeError {
            operation: format!("External: {}", error),
        }
    }
}

/// Convert std::result::Result to Unravel computation
///
/// # Examples
///
/// ```rust
/// use unravel::prelude::*;
/// use unravel::from_result;
///
/// fn parse_number(s: &str) -> Result<i64, std::num::ParseIntError> {
///     s.parse()
/// }
///
/// let computation = from_result(parse_number("42"));
/// let (result, _u) = computation.compute(Universe::new());
/// assert_eq!(result.as_valid(), Some(&42));
/// ```
pub fn from_result<T, E>(result: Result<T, E>) -> impl Compute<Output = T>
where
    E: fmt::Display,
{
    match result {
        Ok(value) => ResultCompute::Valid(Pure::new(value)),
        Err(error) => {
            let void = VoidInfo::new(0, VoidSource::from_external(error));
            ResultCompute::Invalid(Crumble::new(void))
        }
    }
}

/// Internal enum for result computation
enum ResultCompute<T> {
    Valid(Pure<T>),
    Invalid(Crumble<T>),
}

impl<T> Compute for ResultCompute<T> {
    type Output = T;
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<T>, Universe) {
        match self {
            ResultCompute::Valid(pure) => pure.compute(universe),
            ResultCompute::Invalid(crumble) => crumble.compute(universe),
        }
    }
}

/// Extension trait for Result types
pub trait ResultExt<T, E> {
    /// Convert a Result into an Unravel computation
    fn into_unravel(self) -> impl Compute<Output = T>
    where
        E: fmt::Display;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn into_unravel(self) -> impl Compute<Output = T>
    where
        E: fmt::Display,
    {
        from_result(self)
    }
}

/// Macro for using ? operator with Unravel computations
///
/// # Example
///
/// ```rust,ignore
/// use unravel::prelude::*;
/// use unravel::unravel;
///
/// fn example() -> impl Compute<Output = i64> {
///     unravel! {
///         let x = divide(100, 2)?;
///         let y = divide(x, 5)?;
///         Pure::new(y + 10)
///     }
/// }
/// ```
#[macro_export]
macro_rules! unravel {
    ($($tt:tt)*) => {
        compile_error!("unravel! macro is not yet implemented - use .bind() instead")
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_from_result_ok() {
        let result: Result<i64, &str> = Ok(42);
        let computation = from_result(result);
        let (res, _u) = computation.compute(Universe::new());
        assert_eq!(res.as_valid(), Some(&42));
    }
    
    #[test]
    fn test_from_result_err() {
        let result: Result<i64, &str> = Err("something went wrong");
        let computation = from_result(result);
        let (res, u) = computation.compute(Universe::new());
        assert!(res.is_void());
        assert_eq!(u.total_entropy(), 1);
    }
    
    #[test]
    fn test_result_ext() {
        let result: Result<i64, &str> = Ok(42);
        let computation = result.into_unravel();
        let (res, _u) = computation.compute(Universe::new());
        assert_eq!(res.as_valid(), Some(&42));
    }
}
