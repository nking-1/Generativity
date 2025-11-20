# Changelog

## v0.2.0 - Zero-Cost Abstractions (2025-11-20)

### Major Changes

#### 🚀 Zero-Cost Trait-Based Computation System
- **38.61x performance improvement** over heap-based approach
- New `Compute` trait replaces `Box<dyn FnOnce>` pattern
- Fully inlinable computation chains with no heap allocations
- Concrete types: `Pure`, `Crumble`, `Bind`, `Map`, `Recover`, `CombineWith`

#### ⚡ Fork/Join Parallel Semantics
- New `ParallelCombine` combinator with configurable execution modes
- `ParallelMode::Sequential` - times add (single-threaded simulation)
- `ParallelMode::Parallel` - times max (true parallel hardware)
- Universe forking and merging with proven conservation laws

#### 🔧 Ergonomics & Interoperability
- `from_result()` - Convert `std::result::Result<T, E>` to `Unravel`
- `ResultExt` trait - `.into_unravel()` extension method
- Seamless integration with standard Rust error handling
- External errors automatically wrapped as `VoidSource::TypeError`

#### 🧹 Code Quality
- Removed unused `with_entropy` function
- Added `Universe::from_parts` for internal use
- All compiler warnings resolved
- 6 new test cases (19 total tests, all passing)

### Performance Benchmarks

```
Heap-based approach: 159.25µs
Zero-cost approach:  4.125µs
Speedup: 38.61x
```

### Migration Guide

**Old (v0.1) - Heap-based:**
```rust
let result = Unravel::pure(100)
    .bind(|x| divide(x, 2))
    .bind(|y| divide(y, 5));
```

**New (v0.2) - Zero-cost:**
```rust
let result = Bind::new(
    Pure::new(100),
    |x| Bind::new(
        divide_zc(x, 2),
        |y| divide_zc(y, 5)
    )
);
```

The old API still works for convenience, but the new API is recommended for performance-critical code.

### Theory Validation

All changes preserve the mathematical foundation:
- ✅ Gateway theorem still enforced
- ✅ BaseVeil principle (entropy ≥ 1) verified
- ✅ Conservation laws maintained
- ✅ Noether's theorem for logic preserved

### Breaking Changes

None - v0.1 API is fully backward compatible.

### Contributors

- Implementation based on feedback from AI reviewer
- Coq proofs: DAO/Rocq/src/
- Haskell reference: DAO/Rocq/Unravel/haskell/handwritten/

---

## v0.1.0 - Initial Release (2025-11-20)

- Core `Unravel` monad with heap-based closures
- `VoidInfo` and `Universe` types
- Basic operations: divide, add, multiply
- 13 unit tests covering conservation laws
- Example demonstrating thermodynamic computation
