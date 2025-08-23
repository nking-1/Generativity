use super::*;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(test)]
mod arithmetic_stress_tests {
    use super::*;
    
    #[test]
    fn test_integer_overflow_behavior() {
        let max_val = omega!(i32::MAX);
        let one = omega!(1);
        
        // This should overflow in normal arithmetic, let's see what Omega does
        let result = max_val + one;
        
        // Rust's default overflow behavior in debug mode would panic
        // In release mode, it wraps around to i32::MIN
        // Let's see what our Omega does
        match result {
            Omega::Value(v) => println!("Overflow result: {}", v),
            Omega::Void => println!("Overflow became Void"),
        }
        
        // Test multiplication overflow
        let big = omega!(i32::MAX / 2 + 1);
        let overflow_mul = big.clone() * omega!(2);
        println!("Multiplication overflow: {:?}", overflow_mul);
    }
    
    #[test]
    fn test_underflow_behavior() {
        let min_val = omega!(i32::MIN);
        let one = omega!(1);
        
        let result = min_val - one;
        match result {
            Omega::Value(v) => println!("Underflow result: {}", v),
            Omega::Void => println!("Underflow became Void"),
        }
    }
    
    #[test]
    fn test_extreme_division_scenarios() {
        // Division by very small numbers
        let big = omega!(i32::MAX);
        let tiny = omega!(1);
        let result = big / tiny;
        assert_eq!(result, omega!(i32::MAX));
        
        // Division resulting in truncation
        let truncated = omega!(5) / omega!(2);
        assert_eq!(truncated, omega!(2)); // Integer division
        
        // Nested division by zero chains
        let nested_void = (omega!(10) / omega!(0)) / omega!(5);
        assert!(nested_void.is_void());
    }
    
    #[test]
    fn test_modulo_edge_cases() {
        // Modulo with negative numbers
        let neg_result = omega!(-10) % omega!(3);
        println!("Negative modulo: {:?}", neg_result);
        
        // Modulo with i32::MIN (special case in Rust)
        let min_mod = omega!(i32::MIN) % omega!(-1);
        println!("i32::MIN % -1: {:?}", min_mod);
        
        // Large modulo operations
        let large_mod = omega!(i32::MAX) % omega!(7);
        println!("Large modulo: {:?}", large_mod);
    }
    
    #[test]
    fn test_chained_extreme_operations() {
        // Create a computation that would normally panic multiple times
        let dangerous_chain = omega!(i32::MAX)
            .then(|x| omega!(x) + omega!(1))  // Overflow
            .then(|x| omega!(x) / omega!(0))   // Division by zero
            .then(|x| omega!(x) * omega!(i32::MAX)) // Another potential overflow
            .then(|x| omega!(x) % omega!(0));   // Modulo by zero
        
        // This should be void due to the operations
        assert!(dangerous_chain.is_void());
        
        // But we can recover!
        let recovered = dangerous_chain.or(42);
        assert_eq!(recovered, omega!(42));
    }
}

#[cfg(test)]
mod entropy_explosion_tests {
    use super::*;
    
    #[test]
    fn test_exponential_entropy_growth() {
        // Start with a void operation
        let mut current = thermo!(10).divide(thermo!(0));
        assert_eq!(current.entropy, 1);
        
        // Each operation with void increases entropy
        for i in 1..=10 {
            current = current.add(thermo!(10).divide(thermo!(0)));
            println!("Step {}: entropy = {}", i, current.entropy);
        }
        
        // Should have entropy = 1 + (1 + 1) * 10 = 21
        // Each add operation combines entropies and adds 1 for the void result
        assert!(current.entropy >= 10);
    }
    
    #[test]
    fn test_entropy_conservation_under_extreme_recovery() {
        let high_entropy = (0..100).fold(thermo!(0), |acc, _| {
            acc.add(thermo!(10).divide(thermo!(0)))
        });
        
        println!("High entropy before recovery: {}", high_entropy.entropy);
        let original_entropy = high_entropy.entropy;
        
        let recovered = high_entropy.recover(999);
        assert_eq!(recovered.value, omega!(999));
        println!("Entropy after recovery: {}", recovered.entropy);
        
        // Entropy should be conserved!
        assert_eq!(original_entropy, recovered.entropy);
    }
    
    #[test]
    fn test_entropy_limits() {
        // What happens when entropy gets really, really high?
        let mut computation = thermo!(1);
        
        // Add entropy 1000 times
        for _ in 0..1000 {
            computation = computation.add(thermo!(1).divide(thermo!(0)));
        }
        
        println!("Extreme entropy: {}", computation.entropy);
        
        // Should still be recoverable
        let recovered = computation.recover(42);
        assert_eq!(recovered.value, omega!(42));
        assert!(recovered.entropy > 1000);
    }
    
    #[test]
    fn test_entropy_arithmetic_properties() {
        // Test if entropy follows expected mathematical properties
        let a = thermo!(1).divide(thermo!(0)); // entropy 1
        let b = thermo!(2).divide(thermo!(0)); // entropy 1
        let c = thermo!(3).divide(thermo!(0)); // entropy 1
        
        // Test associativity: (a + b) + c = a + (b + c)
        let left = a.clone().add(b.clone()).add(c.clone());
        let right = a.add(b.add(c));
        
        assert_eq!(left.entropy, right.entropy);
        
        // Both should have entropy 5 (3 individual + 2 for operations)
        println!("Associative entropy: {} = {}", left.entropy, right.entropy);
    }
}

#[cfg(test)]
mod memory_stress_tests {
    use super::*;
    
    #[test]
    fn test_deep_computation_chains() {
        let chain_depth = 10000;
        
        let start_time = Instant::now();
        let mut computation = thermo!(1);
        
        // Create a very deep computation chain
        for i in 0..chain_depth {
            computation = computation.add(thermo!(1));
            
            // Every 1000 operations, introduce an error to increase entropy
            if i % 1000 == 0 {
                computation = computation.divide(thermo!(0)).recover(i as i32);
            }
        }
        
        let elapsed = start_time.elapsed();
        println!("Deep chain ({} ops) took {:?}", chain_depth, elapsed);
        println!("Final result: {}", computation);
        
        // Should complete without stack overflow
        assert!(!computation.is_void());
        assert!(computation.entropy > 0);
    }
    
    #[test]
    fn test_wide_computation_trees() {
        // Create many parallel computations
        let width = 1000;
        let mut computations = Vec::new();
        
        let start_time = Instant::now();
        
        for i in 0..width {
            let comp = thermo!(i as i32)
                .divide(thermo!(if i % 10 == 0 { 0 } else { 1 }))
                .recover(999);
            computations.push(comp);
        }
        
        // Combine all computations
        let combined = computations.into_iter().reduce(|acc, comp| acc.add(comp));
        
        let elapsed = start_time.elapsed();
        println!("Wide computation ({} parallel) took {:?}", width, elapsed);
        
        if let Some(result) = combined {
            println!("Combined result: {}", result);
            // Should have accumulated some entropy from the errors
            assert!(result.entropy > 0);
        }
    }
    
    #[test]
    fn test_computation_builder_stress() {
        let operations = 1000;
        
        let start_time = Instant::now();
        let mut builder = ComputationBuilder::start(1000);
        
        for i in 0..operations {
            if i % 2 == 0 {
                builder = builder.then_add(1);
            } else {
                builder = builder.then_divide(if i % 100 == 0 { 0 } else { 2 });
            }
            
            if i % 50 == 0 {
                builder = builder.recover_if_void(i as i32);
            }
        }
        
        let result = builder.build();
        let elapsed = start_time.elapsed();
        
        println!("Builder stress ({} ops) took {:?}", operations, elapsed);
        println!("Builder result: {}", result);
    }
}

#[cfg(test)]
mod concurrency_stress_tests {
    use super::*;
    
    #[test]
    fn test_concurrent_omega_operations() {
        let num_threads = 10;
        let ops_per_thread = 1000;
        let shared_counter = Arc::new(Mutex::new(0));
        let mut handles = vec![];
        
        for thread_id in 0..num_threads {
            let counter = Arc::clone(&shared_counter);
            
            let handle = thread::spawn(move || {
                let mut local_result = omega!(thread_id as i32);
                
                for i in 0..ops_per_thread {
                    local_result = local_result
                        .then(|x| omega!(x + 1))
                        .then(|x| omega!(x).divide(if i % 100 == 0 { 0 } else { 2 }))
                        .or(i as i32);
                    
                    // Occasionally update shared state
                    if i % 100 == 0 {
                        let mut count = counter.lock().unwrap();
                        *count += 1;
                    }
                }
                
                local_result
            });
            
            handles.push(handle);
        }
        
        // Collect all results
        let mut results = vec![];
        for handle in handles {
            results.push(handle.join().unwrap());
        }
        
        println!("Concurrent operations completed");
        println!("Final shared counter: {}", *shared_counter.lock().unwrap());
        
        // All threads should have completed
        assert_eq!(results.len(), num_threads);
        
        // Combine all thread results
        let combined = results.into_iter().reduce(|acc, result| acc + result);
        println!("Combined thread results: {:?}", combined);
    }
    
    #[test]
    fn test_concurrent_thermo_operations() {
        let num_threads = 8;
        let shared_results = Arc::new(Mutex::new(vec![]));
        let mut handles = vec![];
        
        for thread_id in 0..num_threads {
            let results = Arc::clone(&shared_results);
            
            let handle = thread::spawn(move || {
                let mut computation = thermo!(thread_id as i32 * 100);
                
                // Each thread does different error-prone operations
                for i in 0..100 {
                    match thread_id % 4 {
                        0 => computation = computation.divide(thermo!(if i % 10 == 0 { 0 } else { 2 })),
                        1 => computation = computation.add(thermo!(1).divide(thermo!(0))).recover(i as i32),
                        2 => computation = computation.mul(thermo!(2)),
                        3 => computation = computation.add(thermo!(i as i32)),
                        _ => unreachable!(),
                    }
                }
                
                // Store result
                {
                    let mut results_guard = results.lock().unwrap();
                    results_guard.push(computation);
                }
            });
            
            handles.push(handle);
        }
        
        // Wait for all threads
        for handle in handles {
            handle.join().unwrap();
        }
        
        let final_results = shared_results.lock().unwrap();
        println!("Concurrent thermo operations completed");
        
        for (i, result) in final_results.iter().enumerate() {
            println!("Thread {} result: {}", i, result);
        }
        
        // All threads should have produced results
        assert_eq!(final_results.len(), num_threads);
    }
}

#[cfg(test)]
mod performance_degradation_tests {
    use super::*;
    
    #[test]
    fn test_performance_vs_entropy() {
        let operations = 1000;
        
        // Test with low entropy
        let start_time = Instant::now();
        let mut low_entropy = thermo!(100);
        for _ in 0..operations {
            low_entropy = low_entropy.add(thermo!(1));
        }
        let low_entropy_time = start_time.elapsed();
        
        // Test with high entropy
        let start_time = Instant::now();
        let mut high_entropy = thermo!(100).divide(thermo!(0)).recover(100);
        for _ in 0..operations {
            high_entropy = high_entropy.add(thermo!(1).divide(thermo!(0)).recover(1));
        }
        let high_entropy_time = start_time.elapsed();
        
        println!("Low entropy time: {:?}", low_entropy_time);
        println!("High entropy time: {:?}", high_entropy_time);
        println!("Low entropy final: {}", low_entropy);
        println!("High entropy final: {}", high_entropy);
        
        // High entropy operations might be slower due to additional bookkeeping
        // But they should still complete in reasonable time
        assert!(high_entropy_time < Duration::from_secs(1));
    }
    
    #[test]
    fn test_memory_usage_scaling() {
        // This is more of an observational test
        // In a real scenario, you'd use a memory profiler
        
        let small_ops = 100;
        let large_ops = 10000;
        
        let start = Instant::now();
        let mut small_computation = thermo!(0);
        for i in 0..small_ops {
            small_computation = small_computation
                .add(thermo!(1))
                .divide(thermo!(if i % 50 == 0 { 0 } else { 1 }))
                .recover(i as i32);
        }
        let small_time = start.elapsed();
        
        let start = Instant::now();
        let mut large_computation = thermo!(0);
        for i in 0..large_ops {
            large_computation = large_computation
                .add(thermo!(1))
                .divide(thermo!(if i % 50 == 0 { 0 } else { 1 }))
                .recover(i as i32);
        }
        let large_time = start.elapsed();
        
        println!("Small computation ({} ops): {:?}", small_ops, small_time);
        println!("Large computation ({} ops): {:?}", large_ops, large_time);
        
        // Time should scale roughly linearly
        // Handle case where times are too small to measure accurately
        let time_ratio = if small_time.as_nanos() == 0 && large_time.as_nanos() == 0 {
            1.0 // If both are unmeasurably fast, consider them equal
        } else if small_time.as_nanos() == 0 {
            (large_time.as_nanos() as f64).max(1.0) // Avoid division by zero
        } else {
            large_time.as_nanos() as f64 / small_time.as_nanos() as f64
        };
        let ops_ratio = large_ops as f64 / small_ops as f64;
        
        println!("Time scaling ratio: {:.2}", time_ratio);
        println!("Expected ratio: {:.2}", ops_ratio);
        
        // Should not be exponentially worse - but if operations are too fast to measure, that's great!
        if time_ratio.is_finite() {
            assert!(time_ratio < ops_ratio * 10.0, "Performance scaling is worse than expected");
        } else {
            println!("Operations too fast to measure accurately - this is excellent!");
        }
    }
}

#[cfg(test)]
mod pathological_input_tests {
    use super::*;
    
    #[test]
    fn test_extreme_values() {
        // Test with extreme i32 values
        let extreme_cases = vec![
            i32::MAX,
            i32::MIN,
            0,
            -1,
            1,
            i32::MAX - 1,
            i32::MIN + 1,
        ];
        
        for &val in &extreme_cases {
            let omega_val = omega!(val);
            
            // Test all operations with extreme values
            let add_result = omega_val.clone() + omega!(1);
            let sub_result = omega_val.clone() - omega!(1);
            let mul_result = omega_val.clone() * omega!(2);
            let div_result = omega_val.clone() / omega!(2);
            let mod_result = omega_val.clone() % omega!(3);
            
            println!("Value {}: add={:?}, sub={:?}, mul={:?}, div={:?}, mod={:?}", 
                     val, add_result, sub_result, mul_result, div_result, mod_result);
        }
    }
    
    #[test]
    fn test_void_propagation_chains() {
        // Create long chains where void propagates through
        let chain_length = 100;
        let mut computation = omega!(42);
        
        // Introduce void at different points
        for i in 0..chain_length {
            if i == 50 {
                // Introduce void in the middle
                computation = computation / omega!(0);
            } else {
                computation = computation + omega!(1);
            }
        }
        
        // Should be void due to division by zero
        assert!(computation.is_void());
        
        // Test recovery after long void chain
        let recovered = computation.or(999);
        assert_eq!(recovered, omega!(999));
    }
    
    #[test]
    fn test_nested_recovery_patterns() {
        // Test complex recovery scenarios
        let complex_recovery = omega!(100)
            .divide(0)  // becomes void
            .or_else(|| omega!(50).divide(0))  // also void
            .or_else(|| omega!(25).divide(0))  // also void
            .or_else(|| omega!(10))            // finally succeeds
            .then(|x| omega!(x * 2));
        
        assert_eq!(complex_recovery, omega!(20));
    }
    
    #[test]
    fn test_computation_builder_pathological() {
        // Test builder with pathological patterns
        let result = ComputationBuilder::start(i32::MAX)
            .then_add(1)  // Overflow
            .recover_if_void(1000)
            .then_divide(0)  // Division by zero
            .recover_if_void(500)
            .then_add(i32::MIN)  // Another potential overflow
            .recover_if_void(250)
            .build();
        
        println!("Pathological builder result: {}", result);
        // Should have some result, possibly with entropy
    }
}

#[cfg(test)]
mod error_propagation_stress_tests {
    use super::*;
    
    #[test]
    fn test_mixed_error_types() {
        // Combine different types of errors in one computation
        let mixed_errors = thermo!(100)
            .divide(thermo!(0))        // Division by zero
            .add(thermo!(i32::MAX))    // Potential overflow with void
            .mul(thermo!(0))           // Multiplication with recovered value
            .divide(thermo!(-1))       // Division by negative
            .recover(42);
        
        println!("Mixed errors result: {}", mixed_errors);
        assert_eq!(mixed_errors.value, omega!(42));
        assert!(mixed_errors.entropy > 0);
    }
    
    #[test]
    fn test_error_accumulation_patterns() {
        // Test different patterns of error accumulation
        let patterns = vec![
            // Burst errors
            (0..10).fold(thermo!(100), |acc, _| acc.divide(thermo!(0))),
            
            // Gradual errors
            (0..100).fold(thermo!(100), |acc, i| {
                if i % 10 == 0 {
                    acc.divide(thermo!(0))
                } else {
                    acc.add(thermo!(1))
                }
            }),
            
            // Alternating success/failure
            (0..50).fold(thermo!(100), |acc, i| {
                if i % 2 == 0 {
                    acc.add(thermo!(1))
                } else {
                    acc.divide(thermo!(0)).recover(100)
                }
            }),
        ];
        
        for (i, pattern) in patterns.iter().enumerate() {
            println!("Pattern {}: {}", i, pattern);
        }
    }
    
    #[test]
    fn test_recovery_cascades() {
        // Test cascading recovery scenarios
        let cascade = thermo!(1000)
            .divide(thermo!(0))
            .recover(900)
            .divide(thermo!(0))
            .recover(800)
            .divide(thermo!(0))
            .recover(700);
        
        // Each recovery should preserve accumulated entropy
        println!("Recovery cascade: {}", cascade);
        assert_eq!(cascade.value, omega!(700));
        assert_eq!(cascade.entropy, 3);  // Three division-by-zero errors
    }
}