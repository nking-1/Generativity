# Unravel: Thermodynamic Computation in Rust

A monad implementation where error handling respects physical laws.

[![Rust](https://img.shields.io/badge/rust-1.70%2B-orange.svg)](https://www.rust-lang.org/)
[![Tests](https://img.shields.io/badge/tests-19%20passing-brightgreen.svg)](https://github.com/nking-1/Generativity)
[![Performance](https://img.shields.io/badge/performance-38x%20faster-blue.svg)](examples/zero_cost.rs)

## Overview

**Unravel** is a Rust library implementing computational thermodynamics based on the Gateway theorem from the DAO/Rocq mathematical framework. It treats errors not as exceptions to avoid, but as structured encounters with the impossible predicate (`omega_veil`) that has measurable thermodynamic cost.

**Latest:** v0.2 features zero-cost abstractions with **38.61x performance improvement** over the heap-based approach.

## Mathematical Foundation

Based on three key theorems proven in Coq:

1. **Gateway Theorem**: All impossible predicates collapse to a single canonical form (`omega_veil`)
2. **BaseVeil Principle**: Every gateway crossing has entropy ≥ 1
3. **Noether's Theorem for Logic**: Symmetries preserving impossibility correspond to conservation laws

## Core Concepts

### VoidInfo: The Gateway to Impossibility

```rust
pub struct VoidInfo {
    entropy: u64,      // Thermodynamic cost (≥ 1)
    time_step: u64,    // When it happened
    source: VoidSource // Why it happened
}
```

All errors (division by zero, undefined variables, type mismatches) are manifestations of the same underlying impossibility.

### Universe: Thermodynamic State

```rust
pub struct Universe {
    total_entropy: u64,  // Never decreases (Second Law)
    time_step: u64,      // Always advances (Arrow of Time)
    void_count: u64,     // Monotonically increases
}
```

Tracks the physical state of computation with proven conservation laws.

### Unravel<T>: The Monad

```rust
pub struct Unravel<T> {
    run_fn: Box<dyn FnOnce(Universe) -> (UResult<T>, Universe)>
}
```

Threads universe state through computations, automatically tracking entropy.

## Quick Start

### Heap-Based API (Simple, Flexible)

```rust
use unravel::prelude::*;

fn main() {
    // Pure computation (no entropy)
    let pure = Unravel::pure(42);
    
    // Gateway crossing (entropy = 1)
    let void = divide(10, 0);
    
    // Recovery (entropy preserved)
    let recovered = divide(10, 0).recover(42);
    
    // Run and inspect universe
    let (result, universe) = recovered.run();
    println!("Result: {:?}", result);
    println!("Entropy: {}", universe.total_entropy());
}
```

### Zero-Cost API (High Performance)

```rust
use unravel::prelude::*;

fn main() {
    // Same semantics, 38x faster
    let computation = Bind::new(
        Pure::new(100),
        |x| Bind::new(
            divide_zc(x, 2),
            |y| Pure::new(y + 10)
        )
    );
    
    let (result, universe) = computation.compute(Universe::new());
    println!("Result: {:?}", result.as_valid());
    println!("Universe: {}", universe);
}
```

## Examples

Run the examples:

```bash
# Basic thermodynamic computation
cargo run --example basic

# Zero-cost abstractions with benchmarks
cargo run --release --example zero_cost
```

**Performance Results:**
```
Heap-based approach: 159.25µs
Zero-cost approach:  4.125µs
Speedup: 38.61x ⚡
```

## Key Features

- **🚀 Zero-cost abstractions**: 38x faster than heap-based approach (v0.2)
- **✅ Proven correctness**: Based on formal Coq specifications
- **⚖️ Conservation laws**: Entropy tracking with mathematical guarantees
- **🔧 Composable**: Works with standard Rust patterns
- **🔀 Parallel execution**: Fork/Join with sequential or parallel time semantics
- **🤝 std::Result interop**: Seamless integration with existing Rust code

## Theory References

- `DAO/Rocq/src/Scratch/OmegaGateway.v` - Gateway theorem proof
- `DAO/Rocq/src/Computation/UnravelLang.v` - Core Coq specification
- `DAO/Rocq/Unravel/haskell/handwritten/UnravelMonad.hs` - Reference implementation

## Why This Matters

Traditional error handling treats errors as control flow interruptions. Unravel treats them as physical boundaries with thermodynamic cost:

- Errors aren't exceptions - they're structure
- Recovery doesn't erase cost - entropy is conserved
- Computation is physics - the monad enforces conservation laws

This isn't just a different API - it's a different ontology.

## License

MIT OR Apache-2.0
