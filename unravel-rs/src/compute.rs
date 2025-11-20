//! Zero-cost trait-based computation
//!
//! This module replaces the heap-allocated closure approach with a
//! trait-based design that allows full compiler optimization.
//!
//! ## Architecture
//!
//! Instead of `Box<dyn FnOnce>`, we define a trait `Compute` and
//! implement it for concrete types: Pure, Crumble, Bind, Map, etc.
//!
//! The compiler can then inline the entire computation chain into
//! a single state machine, eliminating heap allocations.

use crate::{Universe, UResult, VoidInfo};
use std::marker::PhantomData;

/// Core trait for thermodynamic computations
///
/// This replaces the `Box<dyn FnOnce(Universe) -> (UResult<T>, Universe)>` pattern
/// with a zero-cost abstraction that can be fully inlined.
pub trait Compute {
    type Output;
    
    /// Execute the computation with the given universe state
    fn compute(self, universe: Universe) -> (UResult<Self::Output>, Universe);
}

// ============================================================================
// PRIMITIVE COMPUTATIONS
// ============================================================================

/// Pure computation: lifts a value into the monad
pub struct Pure<T> {
    value: T,
}

impl<T> Pure<T> {
    pub fn new(value: T) -> Self {
        Self { value }
    }
}

impl<T> Compute for Pure<T> {
    type Output = T;
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<T>, Universe) {
        (UResult::Valid(self.value), universe)
    }
}

/// Crumble: creates a void (gateway crossing)
pub struct Crumble<T> {
    info: VoidInfo,
    _phantom: PhantomData<T>,
}

impl<T> Crumble<T> {
    pub fn new(info: VoidInfo) -> Self {
        Self {
            info,
            _phantom: PhantomData,
        }
    }
}

impl<T> Compute for Crumble<T> {
    type Output = T;
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<T>, Universe) {
        let u_evolved = universe.evolve(&self.info);
        (UResult::Void(self.info), u_evolved)
    }
}

// ============================================================================
// COMBINATOR COMPUTATIONS
// ============================================================================

/// Bind: monadic sequencing
pub struct Bind<C, F, T>
where
    C: Compute,
{
    computation: C,
    function: F,
    _phantom: PhantomData<T>,
}

impl<C, F, T> Bind<C, F, T>
where
    C: Compute,
{
    pub fn new(computation: C, function: F) -> Self {
        Self {
            computation,
            function,
            _phantom: PhantomData,
        }
    }
}

impl<C, F, U> Compute for Bind<C, F, C::Output>
where
    C: Compute,
    F: FnOnce(C::Output) -> U,
    U: Compute,
{
    type Output = U::Output;
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<Self::Output>, Universe) {
        let (result, u_prime) = self.computation.compute(universe);
        let u_timed = u_prime.tick();
        
        match result {
            UResult::Valid(val) => {
                let next = (self.function)(val);
                next.compute(u_timed)
            }
            UResult::Void(info) => (UResult::Void(info), u_timed),
        }
    }
}

/// Map: functor mapping
pub struct Map<C, F, T>
where
    C: Compute,
{
    computation: C,
    function: F,
    _phantom: PhantomData<T>,
}

impl<C, F, T> Map<C, F, T>
where
    C: Compute,
{
    pub fn new(computation: C, function: F) -> Self {
        Self {
            computation,
            function,
            _phantom: PhantomData,
        }
    }
}

impl<C, F, U> Compute for Map<C, F, U>
where
    C: Compute,
    F: FnOnce(C::Output) -> U,
{
    type Output = U;
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<U>, Universe) {
        let (result, u_prime) = self.computation.compute(universe);
        (result.map(self.function), u_prime)
    }
}

/// Recover: provides default on void
pub struct Recover<C>
where
    C: Compute,
{
    computation: C,
    default: C::Output,
}

impl<C> Recover<C>
where
    C: Compute,
{
    pub fn new(computation: C, default: C::Output) -> Self {
        Self {
            computation,
            default,
        }
    }
}

impl<C> Compute for Recover<C>
where
    C: Compute,
{
    type Output = C::Output;
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<Self::Output>, Universe) {
        let (result, u_prime) = self.computation.compute(universe);
        match result {
            UResult::Valid(_) => (result, u_prime),
            UResult::Void(_) => (UResult::Valid(self.default), u_prime),
        }
    }
}

/// CombineWith: applicative combination (both branches evaluated)
pub struct CombineWith<C1, C2>
where
    C1: Compute,
    C2: Compute,
{
    computation1: C1,
    computation2: C2,
}

impl<C1, C2> CombineWith<C1, C2>
where
    C1: Compute,
    C2: Compute,
{
    pub fn new(computation1: C1, computation2: C2) -> Self {
        Self {
            computation1,
            computation2,
        }
    }
}

impl<C1, C2> Compute for CombineWith<C1, C2>
where
    C1: Compute,
    C2: Compute,
{
    type Output = (C1::Output, C2::Output);
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<Self::Output>, Universe) {
        // Evaluate first computation
        let (res1, u_prime) = self.computation1.compute(universe);
        // Evaluate second computation
        let (res2, u_double_prime) = self.computation2.compute(u_prime);
        // Time advances
        let u_timed = u_double_prime.tick();
        
        match (res1, res2) {
            (UResult::Valid(v1), UResult::Valid(v2)) => {
                (UResult::Valid((v1, v2)), u_timed)
            }
            (UResult::Void(info), UResult::Valid(_)) => {
                (UResult::Void(info), u_timed)
            }
            (UResult::Valid(_), UResult::Void(info)) => {
                (UResult::Void(info), u_timed)
            }
            (UResult::Void(i1), UResult::Void(i2)) => {
                // Void propagation: entropies add
                let combined = VoidInfo::combine(i1, i2, u_timed.time_step());
                let u_final = u_timed.evolve(&combined);
                (UResult::Void(combined), u_final)
            }
        }
    }
}

// ============================================================================
// PARALLEL COMPUTATIONS (Fork/Join)
// ============================================================================

/// Execution mode for parallel computations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParallelMode {
    /// Sequential: time costs add (single-threaded simulation)
    Sequential,
    
    /// Parallel: time is max (true parallel hardware)
    Parallel,
}

/// ParallelCombine: Fork/Join semantics
///
/// Unlike CombineWith which threads universe state sequentially,
/// this splits the universe, runs both branches independently,
/// then merges the results.
///
/// THEOREM: This preserves conservation laws:
/// - Entropy always adds (irreversible processes are independent)
/// - Time depends on execution mode (sequential vs parallel)
pub struct ParallelCombine<C1, C2>
where
    C1: Compute,
    C2: Compute,
{
    computation1: C1,
    computation2: C2,
    mode: ParallelMode,
}

impl<C1, C2> ParallelCombine<C1, C2>
where
    C1: Compute,
    C2: Compute,
{
    pub fn new(computation1: C1, computation2: C2, mode: ParallelMode) -> Self {
        Self {
            computation1,
            computation2,
            mode,
        }
    }
}

impl<C1, C2> Compute for ParallelCombine<C1, C2>
where
    C1: Compute,
    C2: Compute,
{
    type Output = (C1::Output, C2::Output);
    
    #[inline]
    fn compute(self, universe: Universe) -> (UResult<Self::Output>, Universe) {
        // Fork: Clone universe for independent execution
        let u0_a = universe.clone();
        let u0_b = universe;
        
        // Execute both branches independently
        let (res1, u1) = self.computation1.compute(u0_a);
        let (res2, u2) = self.computation2.compute(u0_b);
        
        // Join: Merge universe states
        let merged_entropy = u1.total_entropy() + u2.total_entropy();
        let merged_time = match self.mode {
            ParallelMode::Sequential => u1.time_step() + u2.time_step(),
            ParallelMode::Parallel => u1.time_step().max(u2.time_step()),
        };
        let merged_voids = u1.void_count() + u2.void_count();
        
        let u_merged = Universe::from_parts(merged_entropy, merged_time, merged_voids);
        
        match (res1, res2) {
            (UResult::Valid(v1), UResult::Valid(v2)) => {
                (UResult::Valid((v1, v2)), u_merged)
            }
            (UResult::Void(info), UResult::Valid(_)) => {
                (UResult::Void(info), u_merged)
            }
            (UResult::Valid(_), UResult::Void(info)) => {
                (UResult::Void(info), u_merged)
            }
            (UResult::Void(i1), UResult::Void(i2)) => {
                let combined = VoidInfo::combine(i1, i2, u_merged.time_step());
                let u_final = u_merged.evolve(&combined);
                (UResult::Void(combined), u_final)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_pure_inlines() {
        let computation = Pure::new(42);
        let (result, _u) = computation.compute(Universe::new());
        assert_eq!(result.as_valid(), Some(&42));
    }
    
    #[test]
    fn test_bind_chains() {
        let computation = Bind::new(
            Pure::new(10),
            |x| Pure::new(x * 2)
        );
        
        let (result, _u) = computation.compute(Universe::new());
        assert_eq!(result.as_valid(), Some(&20));
    }
    
    #[test]
    fn test_parallel_sequential() {
        let comp1 = Pure::new(10);
        let comp2 = Pure::new(20);
        
        let parallel = ParallelCombine::new(comp1, comp2, ParallelMode::Sequential);
        let (_result, u) = parallel.compute(Universe::new());
        
        // In sequential mode, times should add
        assert_eq!(u.time_step(), 0); // Both Pure operations have no time cost
    }
}
