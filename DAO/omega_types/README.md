# Omega: Total Functions Through Computational Thermodynamics 🌀

## Revolutionary Error Handling for Rust

Omega brings total functions to Rust by treating errors as first-class values rather than failures. Inspired by the DAO (Dialectical Autonomy Ontology) framework, every operation always returns a value - even division by zero!

## 🚀 Features

- **No More Panics**: Division by zero? Array out of bounds? These return `Void` (⊥_ω), not crashes
- **Thermodynamic Computing**: Track computational "entropy" - know exactly how many errors occurred
- **Conservation Laws**: Recovery operations preserve entropy (Noether's theorem in code!)
- **Natural Syntax**: Overloaded operators make total functions feel like normal Rust
- **Computational Health**: Entropy tells you if something went wrong, even after recovery

## 📦 Installation

```toml
[dependencies]
omega = "0.1.0"
```

## 🎯 Quick Start

```rust
use omega::*;

// Division by zero? No problem!
let result = omega!(10) / omega!(0);  // Returns Void, doesn't panic
let safe = result.or(999);            // Recover with default: 999

// Track computational health with entropy
let calc = thermo!(100)
    .divide(thermo!(0))     // Fails here (entropy: 1)
    .recover(50);           // Recovers to 50, but entropy remains 1
    
println!("{}", calc);       // "50 [entropy: 1]"
// We got an answer AND know something went wrong!
```

## 💡 Core Concepts

### The Omega Type
```rust
enum Omega<T> {
    Value(T),   // Normal value
    Void,       // Omega_veil (⊥_ω) - the impossible value
}
```

### Thermodynamic Operations
Every operation tracks entropy - a measure of computational "disorder":
- Clean operations: entropy = 0
- Each error adds entropy
- Recovery preserves entropy (conservation law!)

## 🔬 Advanced Examples

### Safe Array Access
```rust
let arr = vec![1, 2, 3];
let element = safe_index(&arr, 10);  // No panic!
let safe = element.or(0);            // Default to 0
```

### Complex Calculations with Health Monitoring
```rust
fn risk_assessment(revenue: i32, costs: i32, market_share: i32) -> ThermoOmega<i32> {
    thermo!(revenue - costs)
        .divide(thermo!(market_share))
        .recover(50)  // Default risk score
}

let risk = risk_assessment(1000, 600, 0);  // Division by zero!
// Returns: 50 (recovered) with entropy: 2 (shows failure occurred)
```

### Builder Pattern for Complex Computations
```rust
let result = ComputationBuilder::start(100)
    .then_divide(10)  // 100/10 = 10
    .then_add(5)      // 10 + 5 = 15  
    .then_divide(3)   // 15/3 = 5
    .recover_if_void(999)
    .build();
```

## 🧬 The Physics of Computation

Omega implements actual thermodynamics in code:

1. **Entropy** tracks accumulated computational errors
2. **Conservation Laws** ensure information is never lost
3. **Noether's Theorem** proves equivalent computations have identical entropy
4. **The Second Law** shows entropy always increases through error propagation

## 🌌 Philosophy
- Every operation is total (always returns)
- Errors are data, not failures
- The void (⊥_ω) is a bridge, not a black hole
- Computation continues through impossibility

## 📊 Comparison

| Traditional Rust | Omega |
|-----------------|--------|
| `panic!` on division by zero | Returns `Void` |
| `Option<T>` for maybe values | `Omega<T>` with thermodynamics |
| No error history after recovery | Entropy tracks full history |
| Errors interrupt flow | Errors flow through computation |

## 🔮 Future Directions

- Generic entropy types for custom error tracking
- Quantum-inspired superposition states
- Parallel universe computations
- Integration with async/await