use std::ops::{Add, Sub, Mul, Div, Rem};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Omega<T> {
    Value(T),
    Void,
}

impl<T> Omega<T> {
    pub fn new(value: T) -> Self {
        Omega::Value(value)
    }
    
    pub fn void() -> Self {
        Omega::Void
    }
    
    pub fn is_void(&self) -> bool {
        matches!(self, Omega::Void)
    }
    
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Omega::Value(v) => v,
            Omega::Void => default,
        }
    }
    
    pub fn or_else<F>(self, f: F) -> Omega<T>
    where
        F: FnOnce() -> Omega<T>
    {
        match self {
            Omega::Value(_) => self,
            Omega::Void => f(),
        }
    }
    
    pub fn or(self, default: T) -> Omega<T> {
        match self {
            Omega::Value(_) => self,
            Omega::Void => Omega::Value(default),
        }
    }
    
    pub fn match_omega<F, G, R>(self, on_value: F, on_void: G) -> R
    where
        F: FnOnce(T) -> R,
        G: FnOnce() -> R,
    {
        match self {
            Omega::Value(v) => on_value(v),
            Omega::Void => on_void(),
        }
    }
    
    pub fn map<U, F>(self, f: F) -> Omega<U>
    where
        F: FnOnce(T) -> U
    {
        match self {
            Omega::Value(v) => Omega::Value(f(v)),
            Omega::Void => Omega::Void,
        }
    }
}

impl<T> From<T> for Omega<T> {
    fn from(value: T) -> Self {
        Omega::Value(value)
    }
}

impl<T> From<Option<T>> for Omega<T> {
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(v) => Omega::Value(v),
            None => Omega::Void,
        }
    }
}

pub type OmegaResult<T> = Omega<T>;

impl<T: fmt::Display> fmt::Display for Omega<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Omega::Value(v) => write!(f, "{}", v),
            Omega::Void => write!(f, "⊥_ω"),
        }
    }
}

impl Omega<i32> {
    pub fn divide(self, divisor: i32) -> Omega<i32> {
        match self {
            Omega::Value(n) => {
                match n.checked_div(divisor) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Division by zero or overflow (i32::MIN / -1)
                }
            }
            Omega::Void => Omega::Void,
        }
    }
    
    pub fn add(self, other: Omega<i32>) -> Omega<i32> {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_add(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Overflow
                }
            }
            _ => Omega::Void,
        }
    }
    
    pub fn sub(self, other: Omega<i32>) -> Omega<i32> {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_sub(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Overflow
                }
            }
            _ => Omega::Void,
        }
    }
    
    pub fn mul(self, other: Omega<i32>) -> Omega<i32> {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_mul(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Overflow
                }
            }
            _ => Omega::Void,
        }
    }
    
    pub fn modulo(self, divisor: i32) -> Omega<i32> {
        match self {
            Omega::Value(n) => {
                match n.checked_rem(divisor) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Handles both division by zero and overflow
                }
            }
            Omega::Void => Omega::Void,
        }
    }
    
    pub fn then<F>(self, f: F) -> Omega<i32> 
    where 
        F: FnOnce(i32) -> Omega<i32>
    {
        match self {
            Omega::Value(v) => f(v),
            Omega::Void => Omega::Void,
        }
    }
}

impl Add for Omega<i32> {
    type Output = Self;
    
    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_add(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Overflow
                }
            }
            _ => Omega::Void,
        }
    }
}

impl Sub for Omega<i32> {
    type Output = Self;
    
    fn sub(self, other: Self) -> Self {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_sub(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Overflow
                }
            }
            _ => Omega::Void,
        }
    }
}

impl Mul for Omega<i32> {
    type Output = Self;
    
    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_mul(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Overflow
                }
            }
            _ => Omega::Void,
        }
    }
}

impl Div for Omega<i32> {
    type Output = Self;
    
    fn div(self, other: Self) -> Self {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_div(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Division by zero or overflow (i32::MIN / -1)
                }
            }
            _ => Omega::Void,
        }
    }
}

impl Rem for Omega<i32> {
    type Output = Self;
    
    fn rem(self, other: Self) -> Self {
        match (self, other) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_rem(b) {
                    Some(result) => Omega::Value(result),
                    None => Omega::Void, // Handles both division by zero and overflow (i32::MIN % -1)
                }
            }
            _ => Omega::Void,
        }
    }
}

#[macro_export]
macro_rules! omega {
    ($val:expr) => {
        Omega::Value($val)
    };
    () => {
        Omega::Void
    };
}

#[derive(Debug, Clone, PartialEq)]
pub struct ThermoOmega<T> {
    pub value: Omega<T>,
    pub entropy: u32,
}

impl<T> ThermoOmega<T> {
    pub fn new(val: T) -> Self {
        ThermoOmega {
            value: Omega::Value(val),
            entropy: 0,
        }
    }
    
    pub fn void() -> Self {
        ThermoOmega {
            value: Omega::Void,
            entropy: 1,
        }
    }
    
    pub fn void_with_entropy(entropy: u32) -> Self {
        ThermoOmega {
            value: Omega::Void,
            entropy,
        }
    }
    
    pub fn is_void(&self) -> bool {
        self.value.is_void()
    }
    
    pub fn entropy(&self) -> u32 {
        self.entropy
    }
}

impl ThermoOmega<i32> {
    pub fn add(self, other: Self) -> Self {
        match (&self.value, &other.value) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_add(*b) {
                    Some(result) => ThermoOmega {
                        value: Omega::Value(result),
                        entropy: self.entropy + other.entropy,
                    },
                    None => ThermoOmega {
                        value: Omega::Void,
                        entropy: self.entropy + other.entropy + 1,
                    }
                }
            }
            _ => ThermoOmega {
                value: Omega::Void,
                entropy: self.entropy + other.entropy + 1,
            }
        }
    }
    
    pub fn divide(self, divisor: Self) -> Self {
        match (&self.value, &divisor.value) {
            (Omega::Value(n), Omega::Value(d)) => {
                if *d == 0 {
                    ThermoOmega {
                        value: Omega::Void,
                        entropy: self.entropy + divisor.entropy + 1,
                    }
                } else {
                    match n.checked_div(*d) {
                        Some(result) => ThermoOmega {
                            value: Omega::Value(result),
                            entropy: self.entropy + divisor.entropy,
                        },
                        None => ThermoOmega {
                            value: Omega::Void,
                            entropy: self.entropy + divisor.entropy + 1,
                        }
                    }
                }
            }
            _ => ThermoOmega {
                value: Omega::Void,
                entropy: self.entropy + divisor.entropy + 1,
            }
        }
    }
    
    pub fn mul(self, other: Self) -> Self {
        match (&self.value, &other.value) {
            (Omega::Value(a), Omega::Value(b)) => {
                match a.checked_mul(*b) {
                    Some(result) => ThermoOmega {
                        value: Omega::Value(result),
                        entropy: self.entropy + other.entropy,
                    },
                    None => ThermoOmega {
                        value: Omega::Void,
                        entropy: self.entropy + other.entropy + 1,
                    }
                }
            }
            _ => ThermoOmega {
                value: Omega::Void,
                entropy: self.entropy + other.entropy + 1,
            }
        }
    }
    
    pub fn recover(self, default: i32) -> Self {
        match self.value {
            Omega::Value(_) => self,
            Omega::Void => ThermoOmega {
                value: Omega::Value(default),
                entropy: self.entropy,
            }
        }
    }
}

impl<T: fmt::Display> fmt::Display for ThermoOmega<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} [entropy: {}]", self.value, self.entropy)
    }
}

#[macro_export]
macro_rules! thermo {
    ($val:expr) => {
        ThermoOmega::new($val)
    };
    () => {
        ThermoOmega::void()
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_basic_omega() {
        let x = Omega::new(42);
        assert!(!x.is_void());
        assert_eq!(x.unwrap_or(0), 42);
        
        let y: Omega<i32> = Omega::void();
        assert!(y.is_void());
        assert_eq!(y.unwrap_or(999), 999);
    }

    #[test]
    fn test_division() {
        let x = Omega::new(10);
        let result = x.divide(2);
        assert_eq!(result, Omega::Value(5));
        
        let y = Omega::new(10);
        let void_result = y.divide(0);
        assert!(void_result.is_void());
        
        let z = Omega::void();
        let still_void = z.divide(5);
        assert!(still_void.is_void());
    }
}

#[cfg(test)]
mod arithmetic_tests {
    use super::*;
    
    #[test]
    fn test_arithmetic_ops() {
        let a = Omega::new(10);
        let b = Omega::new(5);
        assert_eq!(a.clone().add(b.clone()), Omega::Value(15));
        assert_eq!(a.clone().sub(b.clone()), Omega::Value(5));
        assert_eq!(a.clone().mul(b.clone()), Omega::Value(50));
        
        let void = Omega::void();
        assert!(a.clone().add(void.clone()).is_void());
        assert!(void.clone().add(b).is_void());
    }
    
    #[test]
    fn test_modulo() {
        let x = Omega::new(10);
        assert_eq!(x.clone().modulo(3), Omega::Value(1));
        assert!(x.modulo(0).is_void());
    }
    
    #[test]
    fn test_chaining() {
        let result = Omega::new(20)
            .then(|x| Omega::new(x / 2))
            .then(|x| Omega::new(x + 5))
            .then(|x| Omega::new(x * 2));
        
        assert_eq!(result, Omega::Value(30));
        
        let void_chain = Omega::new(10)
            .then(|x| Omega::new(x).divide(0))
            .then(|x| Omega::new(x + 100));
        
        assert!(void_chain.is_void());
    }
}

#[cfg(test)]
mod recovery_tests {
    use super::*;
    
    #[test]
    fn test_recovery_methods() {
        let void: Omega<i32> = Omega::void();
        assert_eq!(void.or(42), Omega::Value(42));
        
        let recovered = Omega::void()
            .or_else(|| Omega::new(10).divide(2));
        assert_eq!(recovered, Omega::Value(5));
        
        let value = Omega::new(100);
        assert_eq!(value.or(42), Omega::Value(100));
    }
    
    #[test]
    fn test_pattern_matching() {
        let result = Omega::new(10).divide(2).match_omega(
            |v| format!("Got value: {}", v),
            || format!("Got void!")
        );
        assert_eq!(result, "Got value: 5");
        
        let void_result = Omega::new(10).divide(0).match_omega(
            |v| format!("Got value: {}", v),
            || format!("Got void!")
        );
        assert_eq!(void_result, "Got void!");
    }
    
    #[test]
    fn test_map() {
        let x = Omega::new(10);
        let doubled = x.map(|v| v * 2);
        assert_eq!(doubled, Omega::Value(20));
        
        let void: Omega<i32> = Omega::void();
        let still_void = void.map(|v| v * 2);
        assert!(still_void.is_void());
    }
    
    #[test]
    fn test_conversions() {
        let omega: Omega<i32> = 42.into();
        assert_eq!(omega, Omega::Value(42));
        
        let some: Omega<i32> = Some(10).into();
        assert_eq!(some, Omega::Value(10));
        
        let none: Omega<i32> = None.into();
        assert!(none.is_void());
    }
    
    #[test]
    fn test_practical_example() {
        fn risky_calculation(x: i32, y: i32, z: i32) -> Omega<i32> {
            Omega::new(x)
                .divide(y)
                .then(|v| Omega::new(v + 10))
                .modulo(z)
                .or(999)
        }
        
        assert_eq!(risky_calculation(20, 2, 3), Omega::Value(2));
        assert_eq!(risky_calculation(20, 0, 3), Omega::Value(999));
        assert_eq!(risky_calculation(20, 2, 0), Omega::Value(999));
    }
}

#[cfg(test)]
mod operator_tests {
    use super::*;
    
    #[test]
    fn test_operators() {
        let a = omega!(10);
        let b = omega!(5);
        
        assert_eq!(a.clone() + b.clone(), omega!(15));
        assert_eq!(a.clone() - b.clone(), omega!(5));
        assert_eq!(a.clone() * b.clone(), omega!(50));
        assert_eq!(a.clone() / b.clone(), omega!(2));
        assert_eq!(a.clone() % omega!(3), omega!(1));
    }
    
    #[test]
    fn test_division_by_zero() {
        let x = omega!(10);
        let zero = omega!(0);
        
        assert!((x / zero).is_void());
    }
    
    #[test]
    fn test_void_propagation_operators() {
        let x = omega!(10);
        let void = omega!();
        
        assert!((x.clone() + void.clone()).is_void());
        assert!((void.clone() * x).is_void());
    }
    
    #[test]
    fn test_chained_operators() {
        let result = (omega!(10) + omega!(5)) * omega!(2) / omega!(3);
        assert_eq!(result, omega!(10));
        
        let void_chain = (omega!(10) / omega!(0)) + omega!(100);
        assert!(void_chain.is_void());
    }
    
    #[test]
    fn test_display() {
        let value = omega!(42);
        assert_eq!(format!("{}", value), "42");
        
        let void: Omega<i32> = omega!();
        assert_eq!(format!("{}", void), "⊥_ω");
    }
    
    #[test]
    fn test_complex_expression() {
        let dangerous = omega!(100) / (omega!(10) - omega!(10));
        assert!(dangerous.is_void());
        
        let safe = dangerous.or(999);
        assert_eq!(safe, omega!(999));
    }
}

#[cfg(test)]
mod thermo_tests {
    use super::*;
    
    #[test]
    fn test_entropy_accumulation() {
        let a = thermo!(10);
        let b = thermo!(5);
        
        let sum = a.add(b);
        assert_eq!(sum.value, omega!(15));
        assert_eq!(sum.entropy, 0);
    }
    
    #[test]
    fn test_void_increases_entropy() {
        let x = thermo!(10);
        let zero = thermo!(0);
        
        let void_result = x.divide(zero);
        assert!(void_result.is_void());
        assert_eq!(void_result.entropy, 1);
    }
    
    #[test]
    fn test_entropy_compounds() {
        let a = thermo!(10).divide(thermo!(0));
        let b = thermo!(20).divide(thermo!(0));
        let combined = a.add(b);
        
        assert!(combined.is_void());
        assert_eq!(combined.entropy, 3);
    }
    
    #[test]
    fn test_recovery_conserves_entropy() {
        let void_calc = thermo!(10).divide(thermo!(0));
        assert_eq!(void_calc.entropy, 1);
        
        let recovered = void_calc.recover(999);
        assert_eq!(recovered.value, omega!(999));
        assert_eq!(recovered.entropy, 1);
    }
    
    #[test]
    fn test_noether_theorem() {
        let calc1 = thermo!(5).add(thermo!(3)).add(thermo!(2));
        let calc2 = thermo!(5).add(thermo!(2).add(thermo!(3)));
        
        assert_eq!(calc1.value, calc2.value);
        assert_eq!(calc1.entropy, calc2.entropy);
    }
    
    #[test]
    fn test_thermodynamic_history() {
        let result = thermo!(100)
            .divide(thermo!(10))
            .add(thermo!(5))
            .divide(thermo!(0))
            .recover(42);
        
        assert_eq!(result.value, omega!(42));
        assert_eq!(result.entropy, 1);
        
        println!("Result: {}", result);
    }
    
    #[test]
    fn test_advanced_noether_symmetries() {
        // Commutative symmetry preserves entropy
        let a = thermo!(10).divide(thermo!(0));  // void with entropy 1
        let b = thermo!(5);
        
        let sum1 = a.clone().add(b.clone());
        let sum2 = b.add(a);
        assert_eq!(sum1.entropy, sum2.entropy);  // Both have entropy 2
        
        // Associative symmetry preserves entropy
        let x = thermo!(1);
        let y = thermo!(2);
        let z = thermo!(3);
        
        let assoc1 = x.clone().add(y.clone()).add(z.clone());
        let assoc2 = x.add(y.add(z));
        assert_eq!(assoc1.entropy, assoc2.entropy);
        
        // Complex refactoring preserves entropy
        // (a * b) + (a * c) = a * (b + c)
        let a = thermo!(2);
        let b = thermo!(3);
        let c = thermo!(4);
        
        // Left side: (a * b) + (a * c) = (2 * 3) + (2 * 4) = 6 + 8 = 14
        let left = a.clone().mul(b.clone()).add(a.clone().mul(c.clone()));
        
        // Right side: a * (b + c) = 2 * (3 + 4) = 2 * 7 = 14
        let right = a.mul(b.add(c));
        
        assert_eq!(left.value, right.value);
        assert_eq!(left.entropy, right.entropy);  // Conservation under refactoring!
    }
}

pub mod practical {
    use super::*;
    
    pub fn safe_index<T: Clone>(arr: &[T], index: usize) -> Omega<T> {
        if index < arr.len() {
            Omega::Value(arr[index].clone())
        } else {
            Omega::Void
        }
    }
    
    pub fn safe_sqrt(x: f64) -> Omega<f64> {
        if x >= 0.0 {
            Omega::Value(x.sqrt())
        } else {
            Omega::Void
        }
    }
    
    pub fn lookup_user(id: u32) -> ThermoOmega<String> {
        if id == 0 {
            ThermoOmega::void()
        } else {
            ThermoOmega::new(format!("User_{}", id))
        }
    }
    
    pub fn risk_assessment(
        revenue: i32,
        costs: i32, 
        market_share: i32
    ) -> ThermoOmega<i32> {
        let profit = thermo!(revenue).add(thermo!(-costs));
        let efficiency = profit.divide(thermo!(market_share));
        let risk_score = efficiency.add(thermo!(0));
        risk_score.recover(50)
    }
}

#[cfg(test)]
mod practical_tests {
    use super::practical::*;
    use super::*;
    
    #[test]
    fn test_safe_array_access() {
        let arr = vec![10, 20, 30];
        
        assert_eq!(safe_index(&arr, 1), omega!(20));
        assert!(safe_index(&arr, 10).is_void());
    }
    
    #[test]
    fn test_safe_sqrt() {
        assert_eq!(safe_sqrt(9.0), omega!(3.0));
        assert!(safe_sqrt(-4.0).is_void());
    }
    
    #[test]
    fn test_database_lookup() {
        let user = lookup_user(42);
        assert_eq!(user.value, omega!("User_42".to_string()));
        assert_eq!(user.entropy, 0);
        
        let missing = lookup_user(0);
        assert!(missing.is_void());
        assert_eq!(missing.entropy, 1);
    }
    
    #[test]
    fn test_risk_assessment() {
        let risk1 = risk_assessment(1000, 600, 20);
        assert_eq!(risk1.value, omega!(20));
        assert_eq!(risk1.entropy, 0);
        
        let risk2 = risk_assessment(1000, 600, 0);
        assert_eq!(risk2.value, omega!(50));
        assert_eq!(risk2.entropy, 2);  // division by zero (1) + add operation with void (1)
    }
    
    #[test]
    fn test_real_world_chain() {
        let calculation = |x: i32, y: i32, z: i32| -> String {
            let result = thermo!(x)
                .divide(thermo!(y))
                .add(thermo!(10))
                .divide(thermo!(z))
                .recover(0);
            
            format!(
                "Result: {}, Health: {}", 
                result.value,
                if result.entropy == 0 { "Perfect" } 
                else { &format!("Warning (entropy: {})", result.entropy) }
            )
        };
        
        assert_eq!(
            calculation(100, 10, 2),
            "Result: 10, Health: Perfect"
        );
        
        assert_eq!(
            calculation(100, 0, 2),
            "Result: 0, Health: Warning (entropy: 3)"
        );
    }
}

pub struct ComputationBuilder {
    current: ThermoOmega<i32>,
}

impl ComputationBuilder {
    pub fn start(value: i32) -> Self {
        ComputationBuilder {
            current: thermo!(value)
        }
    }
    
    pub fn then_add(mut self, value: i32) -> Self {
        self.current = self.current.add(thermo!(value));
        self
    }
    
    pub fn then_divide(mut self, value: i32) -> Self {
        self.current = self.current.divide(thermo!(value));
        self
    }
    
    pub fn recover_if_void(mut self, default: i32) -> Self {
        self.current = self.current.recover(default);
        self
    }
    
    pub fn build(self) -> ThermoOmega<i32> {
        self.current
    }
}

#[cfg(test)]
mod builder_tests {
    use super::*;
    
    #[test]
    fn test_builder_pattern() {
        let result = ComputationBuilder::start(100)
            .then_divide(10)
            .then_add(5)
            .then_divide(3)
            .recover_if_void(999)
            .build();
        
        assert_eq!(result.value, omega!(5));
        assert_eq!(result.entropy, 0);
    }
}