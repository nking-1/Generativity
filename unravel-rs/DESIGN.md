# Design Philosophy

## The Gateway Theorem in Practice

This Rust implementation is a direct translation of the mathematical framework proven in Coq. Understanding the design requires understanding the theory.

### What Is the Gateway?

From `OmegaGateway.v`:

> For any Alpha-like substructure living inside a richer host, there is a canonical "gateway" predicate that has no witnesses inside the substructure. By uniqueness of impossibility, this gateway IS the impossible predicate (omega_veil).

**In plain terms**: Every consistent computational system has a boundary—things it cannot represent. That boundary is unique and canonical.

### How This Differs from Traditional Error Handling

| Traditional Approach | Unravel Approach |
|---------------------|------------------|
| Errors are exceptions to avoid | Errors are structure to acknowledge |
| Multiple error types compete | All errors collapse to omega_veil |
| Recovery erases the failure | Recovery preserves thermodynamic cost |
| Error handling is control flow | Error handling is physics |

### Key Design Decisions

#### 1. Why `'static` Everywhere?

The monad needs to thread universe state through arbitrarily long computation chains. This requires owned values that can be moved into closures. The `'static` bound ensures values live long enough.

**Alternative approaches considered**:
- Using `Rc<RefCell<Universe>>`: Would make the API non-thread-safe
- Using lifetimes: Would require lifetime annotations everywhere, breaking composability
- Cloning universe: Would violate conservation laws (each clone is a separate timeline)

#### 2. Why Not Use `Result<T, VoidInfo>`?

Standard `Result` has different semantics:
- `Result` short-circuits on first error
- Our `Unravel` tracks universe state through all branches
- Applicative `<*>` evaluates BOTH sides (physical reality explores all branches)

#### 3. Why Track Time Separately from Entropy?

Time and entropy are distinct physical quantities:
- **Time**: Advances with every operation (even pure ones)
- **Entropy**: Only increases when crossing the gateway
- **Theorem (Noether)**: Time symmetry → energy conservation; Impossibility symmetry → entropy conservation

Pure operations advance time but not entropy. This distinction is crucial for the physics.

#### 4. Why Is Void Propagation Additive?

From the Coq proof (`combine_voids` in `UnravelLang.v`):

```coq
Definition combine_voids (v1 v2 : VoidInfo) (u : Universe) : VoidInfo :=
  match v1, v2 with
  | VInfo e1 t1 s1, VInfo e2 t2 s2 =>
      VInfo (e1 + e2) u.(time_step) (VoidPropagation v1 v2)
  end.
```

**THEOREM (Impossibility Algebra)**: `Impossible ∧ Impossible = Impossible` with entropy `e1 + e2`.

This isn't a design choice—it's a proven consequence of the Gateway theorem.

### Performance Considerations

#### Zero-Cost Abstractions

The monad compiles down to:
1. Function calls (can be inlined)
2. Enum discriminant checks (single instruction)
3. Integer arithmetic (entropy tracking)

In release mode with optimizations, the overhead is minimal.

#### When to Use This

**Good fit**:
- Systems where failure tracking matters (compilers, interpreters, parsers)
- Domains where conservation laws are meaningful (resource management, physics simulations)
- Code where mathematical correctness is critical

**Not a good fit**:
- High-frequency hot paths where even minimal overhead matters
- Simple scripts where standard `Result` is sufficient
- Systems that don't need thermodynamic accounting

### Extending the Library

#### Adding New Operations

Follow the pattern in `ops.rs`:

```rust
pub fn my_operation(x: i64) -> Unravel<i64> {
    if condition_fails {
        let void = VoidInfo::new(0, VoidSource::MyFailure { ... });
        Unravel::crumble(void)
    } else {
        Unravel::pure(result)
    }
}
```

#### Creating Custom Void Sources

Extend `VoidSource` enum:

```rust
pub enum VoidSource {
    // Existing variants...
    MyCustomFailure { details: String },
}
```

Every new source automatically collapses to omega_veil by the Gateway theorem.

#### Implementing Domain-Specific Semantics

You can wrap `Unravel` in higher-level abstractions:

```rust
pub struct Parser<T> {
    inner: Unravel<T>,
}

impl<T> Parser<T> {
    pub fn parse(input: &str) -> Self {
        // Custom parsing logic using Unravel primitives
    }
}
```

### Common Patterns

#### Sequential Composition

```rust
divide(a, b)
    .bind(|x| multiply(x, c))
    .bind(|y| add(y, d))
```

#### Conditional Recovery

```rust
risky_operation()
    .bind(|x| if x > 0 {
        Unravel::pure(x)
    } else {
        fallback_operation()
    })
```

#### Parallel Evaluation (both branches run)

```rust
let combined = computation1.combine_with(computation2);
// Both computations execute; entropies accumulate
```

### Connection to Theory

Every design decision traces back to proven theorems:

1. **VoidInfo uniqueness** → Gateway theorem
2. **Entropy ≥ 1** → BaseVeil principle
3. **Entropy addition** → Impossibility algebra
4. **Time monotonicity** → Arrow of time
5. **Conservation laws** → Noether's theorem for logic

This isn't "inspired by" the theory—it IS the theory, implemented in Rust.

### Future Directions

Possible extensions while preserving theoretical soundness:

1. **Async support**: `async fn` returning `Unravel<T>`
2. **Parallel execution**: Track entropy across threads
3. **Procedural macros**: Auto-generate `Unravel` wrappers
4. **Type-level tracking**: Encode entropy in types (requires const generics)
5. **Effect system**: Integrate with Rust effect proposals

All extensions must respect the Gateway theorem—no escape hatches allowed.
