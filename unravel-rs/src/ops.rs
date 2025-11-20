//! Common operations with thermodynamic tracking

use crate::{Unravel, VoidInfo, VoidSource};

/// Division with thermodynamic tracking
///
/// IMPLEMENTS: uDiv from Haskell
/// ```haskell
/// uDiv :: Int -> Int -> Unravel Int
/// uDiv _ 0 = crumble DivByZero
/// uDiv n d = return (n `Prelude.div` d)
/// ```
pub fn divide(numerator: i64, denominator: i64) -> Unravel<i64> {
    if denominator == 0 {
        let void = VoidInfo::new(0, VoidSource::DivByZero { numerator });
        Unravel::crumble(void)
    } else {
        Unravel::pure(numerator / denominator)
    }
}

/// Modulo with thermodynamic tracking
pub fn modulo(numerator: i64, denominator: i64) -> Unravel<i64> {
    if denominator == 0 {
        let void = VoidInfo::new(0, VoidSource::ModByZero { numerator });
        Unravel::crumble(void)
    } else {
        Unravel::pure(numerator % denominator)
    }
}

/// Addition (pure operation, no gateway crossing possible)
pub fn add(a: i64, b: i64) -> Unravel<i64> {
    Unravel::pure(a + b)
}

/// Multiplication (pure operation, no gateway crossing possible)
pub fn multiply(a: i64, b: i64) -> Unravel<i64> {
    Unravel::pure(a * b)
}

/// Subtraction (pure operation, no gateway crossing possible)
pub fn subtract(a: i64, b: i64) -> Unravel<i64> {
    Unravel::pure(a - b)
}

/// Checked division (returns Option to avoid panic)
pub fn checked_divide(numerator: i64, denominator: i64) -> Unravel<i64> {
    numerator.checked_div(denominator)
        .map(Unravel::pure)
        .unwrap_or_else(|| {
            let void = VoidInfo::new(0, VoidSource::DivByZero { numerator });
            Unravel::crumble(void)
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_divide_success() {
        let m = divide(10, 2);
        let (result, _u) = m.run();
        assert_eq!(result.as_valid(), Some(&5));
    }
    
    #[test]
    fn test_divide_by_zero() {
        let m = divide(10, 0);
        let (result, u) = m.run();
        
        assert!(result.is_void());
        assert_eq!(u.total_entropy(), 1);  // BaseVeil
        assert_eq!(u.void_count(), 1);
    }
    
    #[test]
    fn test_add() {
        let m = add(10, 20);
        let (result, u) = m.run();
        
        assert_eq!(result.as_valid(), Some(&30));
        assert_eq!(u.total_entropy(), 0);  // No entropy change
    }
    
    #[test]
    fn test_chaining() {
        let m = divide(100, 2)
            .bind(|x| divide(x, 5))
            .bind(|x| add(x, 10));
        
        let (result, _u) = m.run();
        assert_eq!(result.as_valid(), Some(&20));  // 100/2/5 + 10 = 20
    }
}
