/// Prototype for Omega Types V2 - Improved Generic Design
/// This shows how we could make the library much more general and ergonomic

use std::collections::HashMap;
use std::time::SystemTime;

/// Core trait for safe arithmetic operations
pub trait SafeArithmetic: Clone + PartialEq + std::fmt::Debug + Default {
    fn safe_add(self, other: Self) -> Option<Self>;
    fn safe_sub(self, other: Self) -> Option<Self>;
    fn safe_mul(self, other: Self) -> Option<Self>;
    fn safe_div(self, other: Self) -> Option<Self>;
    fn safe_rem(self, other: Self) -> Option<Self>;
}

/// Rich error categorization
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    Overflow,
    Underflow,
    DivisionByZero,
    InvalidInput,
    ConfigurationError,
    NetworkTimeout,
    ParseError,
}

/// Detailed error information
#[derive(Debug, Clone)]
pub struct ErrorInfo {
    pub kind: ErrorKind,
    pub message: Option<String>,
    pub location: Option<&'static str>,
    pub timestamp: SystemTime,
}

/// Enhanced entropy with detailed error tracking
#[derive(Debug, Clone)]
pub struct EntropyInfo {
    pub total_count: u32,
    pub error_categories: HashMap<ErrorKind, u32>,
    pub recent_errors: Vec<ErrorInfo>, // Keep last N errors
}

impl EntropyInfo {
    pub fn new() -> Self {
        Self {
            total_count: 0,
            error_categories: HashMap::new(),
            recent_errors: Vec::new(),
        }
    }
    
    pub fn add_error(&mut self, error: ErrorInfo) {
        self.total_count += 1;
        *self.error_categories.entry(error.kind.clone()).or_insert(0) += 1;
        
        // Keep only last 10 errors to prevent memory growth
        self.recent_errors.push(error);
        if self.recent_errors.len() > 10 {
            self.recent_errors.remove(0);
        }
    }
    
    pub fn combine(&mut self, other: &EntropyInfo) {
        self.total_count += other.total_count;
        for (kind, count) in &other.error_categories {
            *self.error_categories.entry(kind.clone()).or_insert(0) += count;
        }
    }
    
    pub fn overflow_count(&self) -> u32 {
        self.error_categories.get(&ErrorKind::Overflow).copied().unwrap_or(0)
    }
    
    pub fn division_by_zero_count(&self) -> u32 {
        self.error_categories.get(&ErrorKind::DivisionByZero).copied().unwrap_or(0)
    }
    
    pub fn health_score(&self) -> f64 {
        if self.total_count == 0 { 1.0 } else { 1.0 / (1.0 + self.total_count as f64) }
    }
}

/// Generic Omega type that works with any SafeArithmetic type
#[derive(Debug, Clone)]
pub struct OmegaV2<T: SafeArithmetic> {
    value: Option<T>,
    entropy: EntropyInfo,
}

impl<T: SafeArithmetic> OmegaV2<T> {
    /// Create a pure value with no entropy
    pub fn pure(value: T) -> Self {
        Self {
            value: Some(value),
            entropy: EntropyInfo::new(),
        }
    }
    
    /// Create a void value with specified error
    pub fn error(kind: ErrorKind, message: &str) -> Self {
        let mut entropy = EntropyInfo::new();
        entropy.add_error(ErrorInfo {
            kind,
            message: Some(message.to_string()),
            location: None,
            timestamp: SystemTime::now(),
        });
        
        Self {
            value: None,
            entropy,
        }
    }
    
    /// Check if this is void
    pub fn is_void(&self) -> bool {
        self.value.is_none()
    }
    
    /// Get reference to value without ownership issues
    pub fn value(&self) -> Option<&T> {
        self.value.as_ref()
    }
    
    /// Get entropy information
    pub fn entropy(&self) -> &EntropyInfo {
        &self.entropy
    }
    
    /// Extract value with default (no ownership issues)
    pub fn unwrap_or(&self, default: T) -> T {
        self.value.clone().unwrap_or(default)
    }
    
    /// Extract value or compute default based on entropy
    pub fn unwrap_or_else<F>(&self, f: F) -> T 
    where F: FnOnce(&EntropyInfo) -> T 
    {
        match &self.value {
            Some(v) => v.clone(),
            None => f(&self.entropy),
        }
    }
    
    /// Recover with a default value, preserving entropy
    pub fn recover(&self, default: T) -> Self {
        Self {
            value: Some(self.value.clone().unwrap_or(default)),
            entropy: self.entropy.clone(),
        }
    }
    
    /// Add operation with automatic overflow protection
    pub fn add(&self, other: &Self) -> Self {
        match (&self.value, &other.value) {
            (Some(a), Some(b)) => {
                match a.clone().safe_add(b.clone()) {
                    Some(result) => {
                        let mut entropy = self.entropy.clone();
                        entropy.combine(&other.entropy);
                        Self { value: Some(result), entropy }
                    }
                    None => {
                        let mut result = Self::error(ErrorKind::Overflow, "Addition overflow");
                        result.entropy.combine(&self.entropy);
                        result.entropy.combine(&other.entropy);
                        result
                    }
                }
            }
            _ => {
                let mut result = Self::error(ErrorKind::InvalidInput, "Cannot add void values");
                result.entropy.combine(&self.entropy);
                result.entropy.combine(&other.entropy);
                result
            }
        }
    }
    
    /// Subtraction with overflow protection
    pub fn sub(&self, other: &Self) -> Self {
        match (&self.value, &other.value) {
            (Some(a), Some(b)) => {
                match a.clone().safe_sub(b.clone()) {
                    Some(result) => {
                        let mut entropy = self.entropy.clone();
                        entropy.combine(&other.entropy);
                        Self { value: Some(result), entropy }
                    }
                    None => {
                        let mut result = Self::error(ErrorKind::Underflow, "Subtraction underflow");
                        result.entropy.combine(&self.entropy);
                        result.entropy.combine(&other.entropy);
                        result
                    }
                }
            }
            _ => {
                let mut result = Self::error(ErrorKind::InvalidInput, "Cannot subtract void values");
                result.entropy.combine(&self.entropy);
                result.entropy.combine(&other.entropy);
                result
            }
        }
    }
    
    /// Multiplication with overflow protection
    pub fn mul(&self, other: &Self) -> Self {
        match (&self.value, &other.value) {
            (Some(a), Some(b)) => {
                match a.clone().safe_mul(b.clone()) {
                    Some(result) => {
                        let mut entropy = self.entropy.clone();
                        entropy.combine(&other.entropy);
                        Self { value: Some(result), entropy }
                    }
                    None => {
                        let mut result = Self::error(ErrorKind::Overflow, "Multiplication overflow");
                        result.entropy.combine(&self.entropy);
                        result.entropy.combine(&other.entropy);
                        result
                    }
                }
            }
            _ => {
                let mut result = Self::error(ErrorKind::InvalidInput, "Cannot multiply void values");
                result.entropy.combine(&self.entropy);
                result.entropy.combine(&other.entropy);
                result
            }
        }
    }
    
    /// Division with zero-check and overflow protection  
    pub fn div(&self, other: &Self) -> Self {
        match (&self.value, &other.value) {
            (Some(a), Some(b)) => {
                match a.clone().safe_div(b.clone()) {
                    Some(result) => {
                        let mut entropy = self.entropy.clone();
                        entropy.combine(&other.entropy);
                        Self { value: Some(result), entropy }
                    }
                    None => {
                        let mut result = Self::error(ErrorKind::DivisionByZero, "Division by zero or overflow");
                        result.entropy.combine(&self.entropy);
                        result.entropy.combine(&other.entropy);
                        result
                    }
                }
            }
            _ => {
                let mut result = Self::error(ErrorKind::InvalidInput, "Cannot divide void values");
                result.entropy.combine(&self.entropy);
                result.entropy.combine(&other.entropy);
                result
            }
        }
    }
    
    /// Apply a transformation function
    pub fn map<U, F>(&self, f: F) -> OmegaV2<U>
    where 
        U: SafeArithmetic,
        F: FnOnce(&T) -> U
    {
        match &self.value {
            Some(v) => OmegaV2 {
                value: Some(f(v)),
                entropy: self.entropy.clone(),
            },
            None => OmegaV2 {
                value: None,
                entropy: self.entropy.clone(),
            }
        }
    }
    
    /// Chain operations fluently
    pub fn then<F>(&self, f: F) -> Self
    where F: FnOnce(&T) -> Self
    {
        match &self.value {
            Some(v) => {
                let result = f(v);
                let mut combined_entropy = self.entropy.clone();
                combined_entropy.combine(&result.entropy);
                Self {
                    value: result.value,
                    entropy: combined_entropy,
                }
            }
            None => self.clone(),
        }
    }
}

/// Implement SafeArithmetic for standard types
impl SafeArithmetic for i32 {
    fn safe_add(self, other: Self) -> Option<Self> { self.checked_add(other) }
    fn safe_sub(self, other: Self) -> Option<Self> { self.checked_sub(other) }
    fn safe_mul(self, other: Self) -> Option<Self> { self.checked_mul(other) }
    fn safe_div(self, other: Self) -> Option<Self> { self.checked_div(other) }
    fn safe_rem(self, other: Self) -> Option<Self> { self.checked_rem(other) }
}

impl SafeArithmetic for i64 {
    fn safe_add(self, other: Self) -> Option<Self> { self.checked_add(other) }
    fn safe_sub(self, other: Self) -> Option<Self> { self.checked_sub(other) }
    fn safe_mul(self, other: Self) -> Option<Self> { self.checked_mul(other) }
    fn safe_div(self, other: Self) -> Option<Self> { self.checked_div(other) }
    fn safe_rem(self, other: Self) -> Option<Self> { self.checked_rem(other) }
}

impl SafeArithmetic for f64 {
    fn safe_add(self, other: Self) -> Option<Self> { 
        let result = self + other;
        if result.is_finite() { Some(result) } else { None }
    }
    fn safe_sub(self, other: Self) -> Option<Self> { 
        let result = self - other;
        if result.is_finite() { Some(result) } else { None }
    }
    fn safe_mul(self, other: Self) -> Option<Self> { 
        let result = self * other;
        if result.is_finite() { Some(result) } else { None }
    }
    fn safe_div(self, other: Self) -> Option<Self> { 
        if other == 0.0 { return None; }
        let result = self / other;
        if result.is_finite() { Some(result) } else { None }
    }
    fn safe_rem(self, other: Self) -> Option<Self> { 
        if other == 0.0 { return None; }
        let result = self % other;
        if result.is_finite() { Some(result) } else { None }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_generic_arithmetic() {
        // Works with i32
        let a = OmegaV2::pure(10i32);
        let b = OmegaV2::pure(20i32);
        let result = a.add(&b);
        
        assert_eq!(result.unwrap_or(0), 30);
        assert_eq!(result.entropy().total_count, 0);
        
        // Works with i64 
        let c = OmegaV2::pure(1000i64);
        let d = OmegaV2::pure(2000i64);
        let result2 = c.mul(&d);
        
        assert_eq!(result2.unwrap_or(0), 2_000_000);
        assert_eq!(result2.entropy().total_count, 0);
        
        // Works with f64
        let e = OmegaV2::pure(3.14f64);
        let f = OmegaV2::pure(2.0f64);
        let result3 = e.div(&f);
        
        assert!((result3.unwrap_or(0.0) - 1.57).abs() < 0.01);
        assert_eq!(result3.entropy().total_count, 0);
    }
    
    #[test]
    fn test_overflow_handling() {
        let max_val = OmegaV2::pure(i32::MAX);
        let one = OmegaV2::pure(1i32);
        
        let overflow_result = max_val.add(&one);
        
        assert!(overflow_result.is_void());
        assert_eq!(overflow_result.entropy().overflow_count(), 1);
        
        // Can recover with default
        let recovered = overflow_result.recover(0);
        assert_eq!(recovered.unwrap_or(-1), 0);
        assert_eq!(recovered.entropy().overflow_count(), 1); // Entropy preserved
    }
    
    #[test]
    fn test_detailed_error_tracking() {
        let a = OmegaV2::pure(10i32);
        let zero = OmegaV2::pure(0i32);
        
        let div_result = a.div(&zero);
        
        assert!(div_result.is_void());
        assert_eq!(div_result.entropy().division_by_zero_count(), 1);
        assert_eq!(div_result.entropy().total_count, 1);
        
        // Chain more operations
        let b = OmegaV2::pure(i32::MAX);
        let overflow_result = div_result.add(&b);
        
        assert_eq!(overflow_result.entropy().division_by_zero_count(), 1);
        assert_eq!(overflow_result.entropy().total_count, 2); // div by zero + invalid input
    }
    
    #[test]
    fn test_fluent_chaining() {
        let result = OmegaV2::pure(100i32)
            .then(|&x| OmegaV2::pure(x + 50))  // 150
            .then(|&x| OmegaV2::pure(x / 2).div(&OmegaV2::pure(3)))  // 150/2/3 = 25
            .recover(0);
        
        assert_eq!(result.unwrap_or(-1), 25);
        assert_eq!(result.entropy().total_count, 0);
    }
    
    #[test]
    fn test_health_score() {
        let healthy = OmegaV2::pure(42i32);
        assert_eq!(healthy.entropy().health_score(), 1.0);
        
        let unhealthy = OmegaV2::pure(10i32).div(&OmegaV2::pure(0i32));
        assert!(unhealthy.entropy().health_score() < 1.0);
        assert!(unhealthy.entropy().health_score() > 0.0);
    }
}