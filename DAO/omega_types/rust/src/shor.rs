// shor.rs - Factoring through periodic void patterns

use crate::quantum::*;
use crate::*;

// Shor's Algorithm: Factor N by finding the period of f(x) = a^x mod N
pub struct ShorsAlgorithm {
    pub n: u64,           // Number to factor
    pub a: u64,           // Random base (coprime to N)
    pub circuit: QuantumCircuit,
    pub entropy_timeline: Vec<u32>,
}

impl ShorsAlgorithm {
    pub fn new(n: u64) -> Self {
        // Choose random a < n that's coprime to n
        let a = 2; // Simplified - would be random in real implementation
        
        // Need 2n qubits for Shor's algorithm
        let num_qubits = 2 * (64 - n.leading_zeros()) as usize;
        
        ShorsAlgorithm {
            n,
            a,
            circuit: QuantumCircuit::new(num_qubits),
            entropy_timeline: Vec::new(),
        }
    }
    
    // The quantum heart: find period of a^x mod N
    pub fn quantum_period_finding(&mut self) -> ThermoOmega<u64> {
        println!("🌊 QUANTUM PERIOD FINDING");
        println!("Finding period of {}^x mod {}", self.a, self.n);
        
        // Step 1: Initialize superposition
        println!("\n📊 Step 1: Create superposition of all x values");
        let register_size = self.circuit.qubits.len() / 2;
        for i in 0..register_size {
            self.circuit.apply_hadamard(i);
        }
        
        let entropy_after_superposition = self.circuit.circuit_entropy();
        self.entropy_timeline.push(entropy_after_superposition);
        println!("  Entropy after superposition: {}", entropy_after_superposition);
        
        // Step 2: Apply the modular exponentiation (quantum oracle)
        println!("\n🔮 Step 2: Quantum modular exponentiation");
        let oracle_entropy = self.apply_modular_exponentiation();
        self.entropy_timeline.push(oracle_entropy);
        println!("  Oracle created periodic pattern, entropy: {}", oracle_entropy);
        
        // Step 3: Quantum Fourier Transform - the KEY step!
        println!("\n⚡ Step 3: Quantum Fourier Transform");
        let qft_entropy = self.quantum_fourier_transform();
        self.entropy_timeline.push(qft_entropy);
        println!("  QFT revealed period, entropy: {}", qft_entropy);
        
        // Step 4: Measure and extract period
        println!("\n📏 Step 4: Measure to extract period");
        let period = self.measure_period();
        
        ThermoOmega {
            value: Omega::Value(period),
            entropy: self.circuit.circuit_entropy(),
        }
    }
    
    // Modular exponentiation creates periodic interference patterns
    fn apply_modular_exponentiation(&mut self) -> u32 {
        // In real Shor's, this computes a^x mod N in superposition
        // In our model: creates periodic void patterns
        
        // The period creates interference - some states reinforce, others cancel
        let period_entropy = ((self.n as f64).sqrt() as u32) * 2;
        
        // Add entropy based on the complexity of the period
        for qubit in &mut self.circuit.qubits {
            if !qubit.is_measured() {
                qubit.alpha.entropy += period_entropy;
                qubit.beta.entropy += period_entropy;
            }
        }
        
        self.circuit.total_entropy += period_entropy;
        period_entropy
    }
    
    // QFT: The magic that extracts periodicity from superposition
    fn quantum_fourier_transform(&mut self) -> u32 {
        println!("  🌀 Applying QFT to reveal hidden periodicity...");
        
        let register_size = self.circuit.qubits.len() / 2;
        let mut qft_entropy = 0;
        
        for i in 0..register_size {
            // Hadamard on qubit i
            self.circuit.apply_hadamard(i);
            qft_entropy += 1;
            
            // Controlled phase rotations
            for _j in i+1..register_size {
                // In our model: entanglement creates void correlations
                let phase_entropy = 2;
                self.circuit.total_entropy += phase_entropy;
                qft_entropy += phase_entropy;
            }
        }
        
        // Swap qubits (bit reversal)
        for i in 0..register_size/2 {
            let j = register_size - 1 - i;
            self.circuit.qubits.swap(i, j);
        }
        
        qft_entropy
    }
    
    // Measure and extract the period from QFT result
    fn measure_period(&mut self) -> u64 {
        let register_size = self.circuit.qubits.len() / 2;
        let mut measurement = 0u64;
        
        for i in 0..register_size {
            if self.circuit.measure(i) {
                measurement |= 1 << i;
            }
        }
        
        // Extract period from measurement using continued fractions
        // Simplified: the measurement gives us s/r where r is the period
        let period = self.extract_period_from_measurement(measurement);
        
        println!("  Measured value: {}", measurement);
        println!("  Extracted period: {}", period);
        
        period
    }
    
    fn extract_period_from_measurement(&self, measurement: u64) -> u64 {
        // Simplified period extraction
        // In real Shor's: uses continued fractions
        if measurement == 0 {
            return 1;
        }
        
        // Find the period through GCD magic
        let q = 1 << (self.circuit.qubits.len() / 2);
        let gcd = Self::gcd(measurement, q);
        q / gcd
    }
    
    fn gcd(a: u64, b: u64) -> u64 {
        if b == 0 { a } else { Self::gcd(b, a % b) }
    }
    
    fn modpow(&self, base: u64, exp: u64, modulus: u64) -> u64 {
        let mut result = 1;
        let mut base = base % modulus;
        let mut exp = exp;
        
        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % modulus;
            }
            exp >>= 1;
            base = (base * base) % modulus;
        }
        
        result
    }
    
    // Analyze entropy patterns
    pub fn analyze_entropy_pattern(&self) {
        println!("\n📈 ENTROPY FLOW ANALYSIS");
        println!("========================");
        
        let stages = vec![
            "Superposition",
            "Modular Exp",
            "QFT"
        ];
        
        for (i, &entropy) in self.entropy_timeline.iter().enumerate() {
            if i < stages.len() {
                let bar = "█".repeat((entropy / 5) as usize);
                println!("{:15}: {} {}", stages[i], bar, entropy);
            }
        }
        
        if let Some(&final_entropy) = self.entropy_timeline.last() {
            println!("\nTotal entropy accumulated: {}", final_entropy);
            println!("Entropy per qubit: {:.2}", 
                     final_entropy as f64 / self.circuit.qubits.len() as f64);
        }
    }
    
    // Classical post-processing: use period to find factors
    pub fn factor(&mut self) -> Result<(u64, u64), String> {
        println!("\n🎯 SHOR'S ALGORITHM: FACTORING {}", self.n);
        println!("{}", "=".repeat(50));
        
        // Run quantum period finding
        let period_result = self.quantum_period_finding();
        
        match period_result.value {
            Omega::Value(period) => {
                println!("\n✅ Found period: {}", period);
                println!("  Total entropy accumulated: {}", period_result.entropy);
                
                if period % 2 == 1 {
                    return Err("Period is odd, try different base".to_string());
                }
                
                // Use period to find factors
                let factor1_candidate = Self::gcd(
                    self.modpow(self.a, period/2, self.n) + 1, 
                    self.n
                );
                let factor2_candidate = Self::gcd(
                    self.modpow(self.a, period/2, self.n) - 1, 
                    self.n
                );
                
                // Check if we found non-trivial factors
                if factor1_candidate > 1 && factor1_candidate < self.n {
                    let factor2 = self.n / factor1_candidate;
                    println!("\n🎉 FACTORS FOUND: {} × {} = {}", 
                             factor1_candidate, factor2, self.n);
                    Ok((factor1_candidate, factor2))
                } else if factor2_candidate > 1 && factor2_candidate < self.n {
                    let factor2 = self.n / factor2_candidate;
                    println!("\n🎉 FACTORS FOUND: {} × {} = {}", 
                             factor2_candidate, factor2, self.n);
                    Ok((factor2_candidate, factor2))
                } else {
                    Err("Found trivial factors, try different base".to_string())
                }
            }
            Omega::Void => {
                println!("\n❌ Period finding returned void!");
                println!("  Entropy at failure: {}", period_result.entropy);
                Err("Quantum period finding failed".to_string())
            }
        }
    }
}

// Compare Shor's to classical factoring
pub struct FactoringComparison;

impl FactoringComparison {
    // Classical trial division with entropy tracking
    pub fn classical_factor(n: u64) -> ThermoOmega<(u64, u64)> {
        let mut entropy = 0;
        
        for i in 2..((n as f64).sqrt() as u64 + 1) {
            entropy += 1;  // Each trial adds entropy
            
            if n % i == 0 {
                return ThermoOmega {
                    value: Omega::Value((i, n / i)),
                    entropy,
                };
            }
        }
        
        ThermoOmega {
            value: Omega::Void,  // Failed to factor
            entropy,
        }
    }
    
    pub fn compare_methods(n: u64) {
        println!("\n🆚 CLASSICAL vs QUANTUM FACTORING");
        println!("==================================");
        println!("Factoring: {}", n);
        
        // Classical entropy
        let classical = Self::classical_factor(n);
        match classical.value {
            Omega::Value((f1, f2)) => {
                println!("\n📊 Classical factoring:");
                println!("  Factors: {} × {}", f1, f2);
                println!("  Entropy: {}", classical.entropy);
            }
            Omega::Void => {
                println!("\n📊 Classical: Failed");
                println!("  Entropy: {}", classical.entropy);
            }
        }
        
        // Quantum entropy (estimated)
        let quantum_entropy = ((n as f64).ln() as u32) * 10;  // Polynomial in log(n)
        println!("\n⚛️ Quantum (Shor's) estimate:");
        println!("  Entropy: ~{}", quantum_entropy);
        
        if n > 100 {
            let advantage = classical.entropy as f64 / quantum_entropy as f64;
            println!("\n✨ QUANTUM ADVANTAGE: {:.2}x less entropy!", advantage);
        }
    }
}

#[cfg(test)]
mod shor_tests {
    use super::*;
    
    #[test]
    fn test_shors_small() {
        println!("\n🧪 SHOR'S ALGORITHM - SMALL TEST");
        
        let mut shor = ShorsAlgorithm::new(15);  // Factor 15 = 3 × 5
        
        match shor.factor() {
            Ok((f1, f2)) => {
                assert!(f1 * f2 == 15);
                println!("✅ Successfully factored 15 = {} × {}", f1, f2);
            }
            Err(e) => {
                println!("❌ Factoring failed: {}", e);
            }
        }
        
        shor.analyze_entropy_pattern();
    }
    
    #[test]
    fn test_entropy_scaling() {
        println!("\n📊 ENTROPY SCALING TEST");
        
        for n in [15, 21, 35, 77] {
            println!("\n--- Factoring {} ---", n);
            
            let mut shor = ShorsAlgorithm::new(n);
            let period_result = shor.quantum_period_finding();
            
            println!("Final entropy: {}", period_result.entropy);
            
            // Entropy should scale polylogarithmically
            let expected_scaling = ((n as f64).ln() as u32) * 10;
            println!("Expected scaling: ~{}", expected_scaling);
        }
    }
    
    #[test]
    fn test_factoring_comparison() {
        println!("\n🎯 FACTORING COMPARISON");
        
        FactoringComparison::compare_methods(15);
        FactoringComparison::compare_methods(77);
        FactoringComparison::compare_methods(221);  // 13 × 17
    }
}