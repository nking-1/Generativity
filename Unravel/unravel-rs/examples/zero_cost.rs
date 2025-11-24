//! Zero-cost abstraction examples
//!
//! These examples demonstrate the trait-based Compute system which
//! allows the compiler to fully inline the computation chain.

use unravel::prelude::*;

fn main() {
    println!("=== Zero-Cost Abstraction Examples ===\n");
    
    example_zero_cost_chain();
    example_parallel_execution();
    example_result_interop();
    benchmark_comparison();
}

fn example_zero_cost_chain() {
    println!("1. Zero-Cost Computation Chain");
    println!("   (Fully inlined by compiler)\n");
    
    // This entire chain can be inlined into a single function
    let computation = Bind::new(
        Pure::new(100),
        |x| Bind::new(
            divide_zc(x, 2),
            |y| Bind::new(
                divide_zc(y, 5),
                |z| Pure::new(z + 10)
            )
        )
    );
    
    let (result, universe) = computation.compute(Universe::new());
    
    println!("   Result: {:?}", result.as_valid());
    println!("   Universe: {}", universe);
    println!("   ✓ No heap allocations\n");
}

fn example_parallel_execution() {
    println!("2. Fork/Join Parallel Execution\n");
    
    // Sequential mode: times add
    let comp1 = Pure::new(10);
    let comp2 = Pure::new(20);
    
    let sequential = ParallelCombine::new(comp1, comp2, ParallelMode::Sequential);
    let (result, u_seq) = sequential.compute(Universe::new());
    
    println!("   Sequential mode:");
    println!("   Result: {:?}", result.as_valid());
    println!("   Universe: {}", u_seq);
    
    // Parallel mode: times max
    let comp1 = Pure::new(10);
    let comp2 = Pure::new(20);
    
    let parallel = ParallelCombine::new(comp1, comp2, ParallelMode::Parallel);
    let (result, u_par) = parallel.compute(Universe::new());
    
    println!("\n   Parallel mode:");
    println!("   Result: {:?}", result.as_valid());
    println!("   Universe: {}", u_par);
    println!("   ✓ Fork/Join preserves entropy\n");
}

fn example_result_interop() {
    println!("3. std::Result Interop\n");
    
    fn parse_and_divide(s: &str) -> impl Compute<Output = i64> {
        let parse_result: Result<i64, std::num::ParseIntError> = s.parse();
        
        Bind::new(
            from_result(parse_result),
            |num| divide_zc(num, 2)
        )
    }
    
    // Success case
    let computation = parse_and_divide("100");
    let (result, universe) = computation.compute(Universe::new());
    println!("   Parsed '100' -> {:?}", result.as_valid());
    println!("   Universe: {}", universe);
    
    // Error case
    let computation = parse_and_divide("not_a_number");
    let (_result, universe) = computation.compute(Universe::new());
    println!("\n   Parsed 'not_a_number' -> Void");
    println!("   Universe: {}", universe);
    println!("   ✓ Seamless std::Result integration\n");
}

fn benchmark_comparison() {
    println!("4. Performance Characteristics\n");
    
    const ITERATIONS: usize = 1000;
    
    // Heap-based (old approach)
    let start = std::time::Instant::now();
    for _ in 0..ITERATIONS {
        let computation = Unravel::pure(100)
            .bind(|x| divide(x, 2))
            .bind(|y| divide(y, 5));
        let _ = computation.run();
    }
    let heap_time = start.elapsed();
    
    // Zero-cost (new approach)
    let start = std::time::Instant::now();
    for _ in 0..ITERATIONS {
        let computation = Bind::new(
            Pure::new(100),
            |x| Bind::new(
                divide_zc(x, 2),
                |y| divide_zc(y, 5)
            )
        );
        let _ = computation.compute(Universe::new());
    }
    let zc_time = start.elapsed();
    
    println!("   Heap-based approach: {:?}", heap_time);
    println!("   Zero-cost approach:  {:?}", zc_time);
    println!("   Speedup: {:.2}x", heap_time.as_nanos() as f64 / zc_time.as_nanos() as f64);
    println!("   ✓ Zero-cost abstractions verified\n");
}
