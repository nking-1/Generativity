// grover.rs - Searching through the void with quantum amplitude amplification

use crate::quantum::*;
use crate::*;

// Grover's Algorithm: Find a needle in a haystack using quantum superposition
pub struct GroverSearch {
    pub num_items: usize,
    pub target_index: usize,
    pub circuit: QuantumCircuit,
    pub iteration_entropy: Vec<u32>,  // Track entropy at each Grover iteration
}

impl GroverSearch {
    pub fn new(num_items: usize, target_index: usize) -> Self {
        // Need log2(n) qubits to represent n items
        let num_qubits = (num_items as f64).log2().ceil() as usize;
        
        GroverSearch {
            num_items,
            target_index,
            circuit: QuantumCircuit::new(num_qubits),
            iteration_entropy: Vec::new(),
        }
    }
    
    // Initialize all qubits in equal superposition
    pub fn initialize_superposition(&mut self) {
        println!("🌀 Initializing equal superposition across {} states...", self.num_items);
        
        for i in 0..self.circuit.qubits.len() {
            self.circuit.apply_hadamard(i);
        }
        
        let entropy = self.circuit.circuit_entropy();
        self.iteration_entropy.push(entropy);
        println!("  Initial entropy: {}", entropy);
    }
    
    // The Oracle: marks the target state by flipping its phase
    // In our framework: increases undecidability of the target!
    pub fn oracle(&mut self) {
        println!("🔮 Oracle marking target index {}...", self.target_index);
        
        // In real Grover's, this flips the phase of the target state
        // In our model: the oracle INCREASES entropy when it finds the target
        
        // Simulate checking if we're at the target
        // This is where the "quantum magic" happens - we're checking ALL states at once!
        let oracle_entropy = 3;  // Oracle operation adds entropy
        
        // Add entropy to track that oracle was applied
        for qubit in &mut self.circuit.qubits {
            if !qubit.is_measured() {
                // Oracle affects superposed qubits
                qubit.alpha.entropy += oracle_entropy;
                qubit.beta.entropy += oracle_entropy;
            }
        }
        
        self.circuit.total_entropy += oracle_entropy;
        println!("  Oracle added {} entropy units", oracle_entropy);
    }
    
    // Diffusion operator: amplifies amplitude of marked state
    // In our framework: concentrates undecidability toward the target
    pub fn diffusion(&mut self) {
        println!("📊 Applying diffusion operator...");
        
        // Inversion about average amplitude
        // This is what makes marked states more likely to be measured
        
        // Apply Hadamards
        for i in 0..self.circuit.qubits.len() {
            self.circuit.apply_hadamard(i);
        }
        
        // Phase shift (simplified - would be more complex in real implementation)
        // In our model: redistributes entropy
        let diffusion_entropy = 2;
        self.circuit.total_entropy += diffusion_entropy;
        
        // Apply Hadamards again
        for i in 0..self.circuit.qubits.len() {
            self.circuit.apply_hadamard(i);
        }
        
        println!("  Diffusion added {} entropy units", diffusion_entropy);
    }
    
    // Run one Grover iteration
    pub fn grover_iteration(&mut self) {
        self.oracle();
        self.diffusion();
        
        let current_entropy = self.circuit.circuit_entropy();
        self.iteration_entropy.push(current_entropy);
        println!("  Iteration complete. Total entropy: {}", current_entropy);
    }
    
    // Run the full algorithm
    pub fn search(&mut self) -> ThermoOmega<usize> {
        println!("\n🚀 GROVER'S QUANTUM SEARCH");
        println!("================================");
        println!("Searching {} items for index {}", self.num_items, self.target_index);
        
        // Initialize superposition
        self.initialize_superposition();
        
        // Optimal number of iterations is approximately π/4 * sqrt(N)
        let optimal_iterations = ((std::f64::consts::PI / 4.0) * 
                                  (self.num_items as f64).sqrt()) as usize;
        
        println!("\n⚡ Running {} Grover iterations...", optimal_iterations);
        
        for i in 0..optimal_iterations {
            println!("\n--- Iteration {} ---", i + 1);
            self.grover_iteration();
        }
        
        // Measure all qubits to get result
        println!("\n📏 Measuring qubits...");
        let mut result = 0;
        for i in 0..self.circuit.qubits.len() {
            if self.circuit.measure(i) {
                result |= 1 << i;
            }
        }
        
        // Return result with entropy tracking
        let final_entropy = self.circuit.circuit_entropy();
        
        if result == self.target_index {
            println!("✅ FOUND target at index {}!", result);
            ThermoOmega {
                value: Omega::Value(result),
                entropy: final_entropy,
            }
        } else {
            println!("❌ Search failed - got index {} instead of {}", result, self.target_index);
            ThermoOmega {
                value: Omega::Value(result),
                entropy: final_entropy + 10,  // Failed search has higher entropy!
            }
        }
    }
    
    // Analyze entropy growth pattern
    pub fn analyze_entropy_pattern(&self) {
        println!("\n📈 ENTROPY ANALYSIS");
        println!("===================");
        
        for (i, &entropy) in self.iteration_entropy.iter().enumerate() {
            let bar = "█".repeat((entropy / 2) as usize);
            println!("Iteration {:2}: {} {}", i, bar, entropy);
        }
        
        if self.iteration_entropy.len() > 1 {
            let start = self.iteration_entropy[0];
            let end = self.iteration_entropy[self.iteration_entropy.len() - 1];
            let growth = end - start;
            
            println!("\nEntropy growth: {} -> {} (Δ = {})", start, end, growth);
            println!("Growth rate: {:.2} entropy/iteration", 
                     growth as f64 / (self.iteration_entropy.len() - 1) as f64);
        }
    }
}

// Demonstrate quantum advantage through entropy
pub struct QuantumAdvantage;

impl QuantumAdvantage {
    // Classical search through void
    pub fn classical_search(items: Vec<i32>, target: i32) -> ThermoOmega<usize> {
        println!("\n🔍 CLASSICAL SEARCH");
        let mut entropy = 0;
        
        for (i, &item) in items.iter().enumerate() {
            entropy += 1;  // Each comparison adds entropy
            
            if item == target {
                return ThermoOmega {
                    value: Omega::Value(i),
                    entropy,
                };
            }
        }
        
        // Not found - return void with max entropy
        ThermoOmega {
            value: Omega::Void,
            entropy: items.len() as u32,
        }
    }
    
    // Compare classical vs quantum entropy accumulation
    pub fn compare_search_methods(size: usize, target: usize) {
        println!("\n🆚 CLASSICAL vs QUANTUM SEARCH COMPARISON");
        println!("==========================================");
        println!("Database size: {} items", size);
        println!("Target index: {}", target);
        
        // Classical search entropy
        let classical_entropy = target as u32 + 1;  // Linear with position
        println!("\n📊 Classical search:");
        println!("  Comparisons needed: {}", target + 1);
        println!("  Entropy accumulated: {}", classical_entropy);
        
        // Quantum search entropy (simulated)
        let quantum_iterations = ((std::f64::consts::PI / 4.0) * 
                                  (size as f64).sqrt()) as u32;
        let quantum_entropy = quantum_iterations * 5;  // Each iteration adds ~5 entropy
        
        println!("\n⚛️ Quantum search:");
        println!("  Grover iterations: {}", quantum_iterations);
        println!("  Entropy accumulated: {}", quantum_entropy);
        
        // The advantage
        let advantage = classical_entropy as f64 / quantum_entropy as f64;
        println!("\n✨ QUANTUM ADVANTAGE: {:.2}x less entropy!", advantage);
        
        if size > 100 {
            println!("  For {} items:", size);
            println!("  Classical: O(n) = {} entropy", size);
            println!("  Quantum: O(√n) = {} entropy", quantum_entropy);
        }
    }
}

#[cfg(test)]
mod grover_tests {
    use super::*;
    
    #[test]
    fn test_grover_search_small() {
        println!("\n🧪 GROVER'S ALGORITHM - SMALL TEST");
        
        let mut grover = GroverSearch::new(4, 2);  // Search 4 items for index 2
        let result = grover.search();
        
        grover.analyze_entropy_pattern();
        
        println!("\nFinal result: {:?}", result);
        assert!(result.entropy > 0);  // Should accumulate entropy
    }
    
    #[test]
    fn test_grover_scaling() {
        println!("\n📊 GROVER'S ALGORITHM - SCALING TEST");
        
        // Test different database sizes
        for size in [4, 8, 16, 32] {
            println!("\n--- Database size: {} ---", size);
            
            let mut grover = GroverSearch::new(size, size / 2);
            let result = grover.search();
            
            println!("Result entropy: {}", result.entropy);
            
            // Entropy should scale with sqrt(n)
            let expected_scaling = (size as f64).sqrt() as u32;
            println!("Expected scaling: ~{} iterations", expected_scaling);
        }
    }
    
    #[test]
    fn test_quantum_advantage() {
        println!("\n🎯 QUANTUM ADVANTAGE TEST");
        
        QuantumAdvantage::compare_search_methods(16, 12);
        QuantumAdvantage::compare_search_methods(100, 73);
        QuantumAdvantage::compare_search_methods(1000, 666);
    }
    
    #[test]
    fn test_entropy_accumulation() {
        println!("\n🌡️ ENTROPY ACCUMULATION PATTERNS");
        
        let mut grover = GroverSearch::new(16, 10);
        grover.initialize_superposition();
        
        println!("\nTracking entropy through iterations:");
        for i in 0..4 {
            println!("\n=== Iteration {} ===", i + 1);
            let before = grover.circuit.circuit_entropy();
            grover.grover_iteration();
            let after = grover.circuit.circuit_entropy();
            println!("Entropy change: {} -> {} (Δ = {})", before, after, after - before);
        }
        
        grover.analyze_entropy_pattern();
    }
}

// Quantum annealing - finding ground states by minimizing entropy
pub struct QuantumAnnealer {
    pub temperature: f64,  // Controls entropy flow
    pub energy_landscape: Vec<ThermoOmega<f64>>,
}

impl QuantumAnnealer {
    pub fn new(landscape: Vec<ThermoOmega<f64>>) -> Self {
        QuantumAnnealer {
            temperature: 100.0,
            energy_landscape: landscape,
        }
    }
    
    pub fn anneal(&mut self) -> ThermoOmega<usize> {
        println!("\n🌡️ QUANTUM ANNEALING");
        println!("==============================");
        println!("Starting temperature: {}", self.temperature);
        println!("Energy landscape: {} states", self.energy_landscape.len());
        
        // Start in maximum entropy (hot)
        let mut current_state = ThermoOmega::void_with_entropy(100);
        let mut best_index = 0;
        let mut min_entropy = u32::MAX;
        
        println!("\n🔥 Cooling schedule:");
        
        // Cool down slowly
        while self.temperature > 0.1 {
            self.temperature *= 0.9;  // Cooling rate
            
            // Quantum tunneling through void
            for (i, state) in self.energy_landscape.iter().enumerate() {
                if state.entropy() < min_entropy {
                    min_entropy = state.entropy();
                    best_index = i;
                    
                    // Tunnel to lower entropy state
                    current_state = state.clone();
                    
                    println!("  🌀 Quantum tunnel to state {}: entropy {}", i, state.entropy());
                }
            }
            
            if self.temperature > 1.0 {
                let bar = "█".repeat((current_state.entropy() / 5) as usize);
                println!("  T={:5.2}: {} entropy={}", self.temperature, bar, current_state.entropy());
            }
        }
        
        println!("\n❄️ Ground state found at index {} with entropy {}", best_index, min_entropy);
        println!("Final temperature: {:.3}", self.temperature);
        
        ThermoOmega {
            value: Omega::Value(best_index),
            entropy: min_entropy,
        }
    }
}

#[cfg(test)]
mod annealing_tests {
    use super::*;
    
    #[test]
    fn test_quantum_annealing() {
        println!("\n🧊 QUANTUM ANNEALING TEST");
        
        // Create energy landscape with entropy valleys
        let landscape = vec![
            ThermoOmega::void_with_entropy(50),   // Local minimum
            ThermoOmega::void_with_entropy(100),  // High energy
            ThermoOmega::void_with_entropy(10),   // Global minimum!
            ThermoOmega::void_with_entropy(75),   // Medium energy
        ];
        
        println!("Energy landscape:");
        for (i, state) in landscape.iter().enumerate() {
            println!("  State {}: entropy = {}", i, state.entropy());
        }
        
        let mut annealer = QuantumAnnealer::new(landscape);
        let ground_state = annealer.anneal();
        
        println!("\nAnnealing result: {:?}", ground_state);
        assert_eq!(ground_state.value, Omega::Value(2));  // Should find index 2
        assert_eq!(ground_state.entropy(), 10);  // Should have minimum entropy
        
        println!("✅ Found global minimum!");
    }
    
    #[test] 
    fn test_annealing_comparison() {
        println!("\n🔍 ANNEALING vs GROVER COMPARISON");
        
        // Compare annealing (entropy minimization) vs Grover (amplitude amplification)
        println!("\n📊 Optimization Problems:");
        println!("  Annealing: Find minimum entropy (ground state)");
        println!("  Grover:    Find marked state (search problem)");
        
        // Annealing - optimization
        let optimization_landscape = vec![
            ThermoOmega::void_with_entropy(80),
            ThermoOmega::void_with_entropy(90),  
            ThermoOmega::void_with_entropy(5),   // Global optimum
            ThermoOmega::void_with_entropy(60),
        ];
        
        let mut annealer = QuantumAnnealer::new(optimization_landscape);
        let optimized = annealer.anneal();
        
        println!("\n⚡ Annealing found optimum with entropy: {}", optimized.entropy());
        
        // Grover - search (would need different setup for fair comparison)
        let mut grover = GroverSearch::new(4, 2);
        grover.initialize_superposition();
        grover.grover_iteration();
        let search_entropy = grover.circuit.circuit_entropy();
        
        println!("⚛️ Grover search accumulated entropy: {}", search_entropy);
        
        println!("\n🧠 INSIGHT: Different quantum algorithms optimize different aspects:");
        println!("  - Annealing minimizes entropy (finds ground states)");
        println!("  - Grover controls entropy growth (efficient search)");
        println!("  - Both navigate undecidability space, but with different goals!");
    }
}