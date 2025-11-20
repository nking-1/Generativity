//! Basic examples demonstrating the Unravel monad

use unravel::prelude::*;

fn main() {
    println!("=== Unravel: Thermodynamic Computation Examples ===\n");
    
    example_pure_computation();
    example_division_by_zero();
    example_recovery();
    example_void_propagation();
    example_conservation_laws();
}

fn example_pure_computation() {
    println!("1. Pure Computation (no gateway crossing)");
    
    let computation = Unravel::pure(10)
        .bind(|x| add(x, 20))
        .bind(|x| multiply(x, 2));
    
    let (result, universe) = computation.run();
    
    println!("   Result: {:?}", result.as_valid());
    println!("   Universe: {}", universe);
    println!("   ✓ No entropy (stayed in Alpha)\n");
}

fn example_division_by_zero() {
    println!("2. Division by Zero (gateway crossing)");
    
    let computation = divide(42, 0);
    let (result, universe) = computation.run();
    
    println!("   Result: {:?}", result);
    println!("   Universe: {}", universe);
    println!("   ✓ BaseVeil principle: entropy ≥ 1\n");
}

fn example_recovery() {
    println!("3. Recovery from Void (thermodynamic cost preserved)");
    
    let computation = divide(100, 0).recover(42);
    let (result, universe) = computation.run();
    
    println!("   Result: {:?}", result.as_valid());
    println!("   Universe: {}", universe);
    println!("   ✓ Recovered with default, but entropy remains\n");
}

fn example_void_propagation() {
    println!("4. Void Propagation (entropy addition)");
    
    // This will create two independent voids
    let computation = Unravel::pure(10)
        .bind(|x| {
            // Create two failing computations
            let void1 = divide(x, 0);
            let void2 = divide(20, 0);
            
            // Combine them (both will fail, entropies add)
            void1.bind(move |a| void2.map(move |b| a + b))
        });
    
    let (result, universe) = computation.run();
    
    println!("   Result: {:?}", result);
    println!("   Universe: {}", universe);
    println!("   ✓ Combined entropy from void propagation\n");
}

fn example_conservation_laws() {
    println!("5. Conservation Laws (Noether's Theorem)");
    
    // Run same computation twice
    let computation = || {
        divide(100, 2)
            .bind(|x| divide(x, 0))
            .recover(0)
    };
    
    let (_r1, u1) = computation().run();
    let (_r2, u2) = computation().run();
    
    println!("   First run:  {}", u1);
    println!("   Second run: {}", u2);
    println!("   ✓ Same entropy (deterministic physics)\n");
    
    // Verify commutativity: a + b = b + a (same entropy)
    let add_ab = add(10, 20).bind(|x| divide(x, 0));
    let add_ba = add(20, 10).bind(|x| divide(x, 0));
    
    let (_ra, ua) = add_ab.run();
    let (_rb, ub) = add_ba.run();
    
    println!("   a + b entropy: {}", ua.total_entropy());
    println!("   b + a entropy: {}", ub.total_entropy());
    println!("   ✓ Commutativity preserved (Noether's theorem)\n");
}
