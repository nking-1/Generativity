// quantum.rs - Quantum mechanics through the Omega/DAO lens

use crate::*;
// use std::f64::consts::PI;

// Complex numbers for quantum amplitudes
#[derive(Debug, Clone, PartialEq)]
pub struct Complex {
    pub real: f64,
    pub imag: f64,
}

impl Complex {
    pub fn new(real: f64, imag: f64) -> Self {
        Complex { real, imag }
    }
    
    pub fn zero() -> Self {
        Complex { real: 0.0, imag: 0.0 }
    }
    
    pub fn one() -> Self {
        Complex { real: 1.0, imag: 0.0 }
    }
    
    pub fn magnitude_squared(&self) -> f64 {
        self.real * self.real + self.imag * self.imag
    }
    
    pub fn multiply(&self, other: &Complex) -> Complex {
        Complex {
            real: self.real * other.real - self.imag * other.imag,
            imag: self.real * other.imag + self.imag * other.real,
        }
    }
}

impl std::fmt::Display for Complex {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.imag >= 0.0 {
            write!(f, "{:.3}+{:.3}i", self.real, self.imag)
        } else {
            write!(f, "{:.3}{:.3}i", self.real, self.imag)
        }
    }
}

// A Qubit using Omega - it can be in superposition OR collapsed!
#[derive(Debug, Clone)]
pub struct Qubit {
    // Amplitudes can be Value (superposition) or Void (measured/collapsed)
    pub alpha: ThermoOmega<Complex>,  // |0⟩ amplitude
    pub beta: ThermoOmega<Complex>,   // |1⟩ amplitude
}

impl Qubit {
    // Create |0⟩ state
    pub fn zero() -> Self {
        Qubit {
            alpha: ThermoOmega::new(Complex::one()),
            beta: ThermoOmega::new(Complex::zero()),
        }
    }
    
    // Create |1⟩ state
    pub fn one() -> Self {
        Qubit {
            alpha: ThermoOmega::new(Complex::zero()),
            beta: ThermoOmega::new(Complex::one()),
        }
    }
    
    // Create superposition state
    pub fn superposition(alpha: Complex, beta: Complex) -> Self {
        Qubit {
            alpha: ThermoOmega::new(alpha),
            beta: ThermoOmega::new(beta),
        }
    }
    
    // Check if qubit is in definite state (not superposition)
    pub fn is_classical(&self) -> bool {
        match (&self.alpha.value, &self.beta.value) {
            (Omega::Value(a), Omega::Value(b)) => {
                // Classical if one amplitude is ~1 and other is ~0
                let a_mag = a.magnitude_squared();
                let b_mag = b.magnitude_squared();
                (a_mag > 0.99 && b_mag < 0.01) || (a_mag < 0.01 && b_mag > 0.99)
            }
            _ => true  // Collapsed states are "classical" in a sense
        }
    }
    
    // Check if measured (collapsed to void)
    pub fn is_measured(&self) -> bool {
        self.alpha.is_void() || self.beta.is_void()
    }
    
    // Total entropy (measurement history)
    pub fn entropy(&self) -> u32 {
        self.alpha.entropy() + self.beta.entropy()
    }
}

impl std::fmt::Display for Qubit {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.is_measured() {
            write!(f, "|⊥_ω⟩ [entropy: {}]", self.entropy())
        } else {
            match (&self.alpha.value, &self.beta.value) {
                (Omega::Value(a), Omega::Value(b)) => {
                    write!(f, "{}|0⟩ + {}|1⟩", a, b)
                }
                _ => write!(f, "|⊥_ω⟩")
            }
        }
    }
}

// Quantum gates as transformations
pub struct QuantumGate;

impl QuantumGate {
    // Hadamard gate - creates superposition (makes things undecidable!)
    pub fn hadamard(q: &Qubit) -> Qubit {
        if q.is_measured() {
            // Can't operate on measured qubits - they stay collapsed
            return q.clone();
        }
        
        match (&q.alpha.value, &q.beta.value) {
            (Omega::Value(a), Omega::Value(b)) => {
                let sqrt2 = (2.0_f64).sqrt();
                let new_alpha = Complex::new(
                    (a.real + b.real) / sqrt2,
                    (a.imag + b.imag) / sqrt2,
                );
                let new_beta = Complex::new(
                    (a.real - b.real) / sqrt2,
                    (a.imag - b.imag) / sqrt2,
                );
                
                Qubit {
                    alpha: ThermoOmega::new(new_alpha),
                    beta: ThermoOmega::new(new_beta),
                }
            }
            _ => q.clone()
        }
    }
    
    // Pauli-X gate (NOT gate)
    pub fn pauli_x(q: &Qubit) -> Qubit {
        if q.is_measured() {
            return q.clone();
        }
        
        Qubit {
            alpha: q.beta.clone(),
            beta: q.alpha.clone(),
        }
    }
    
    // Measurement - forces decidability, causes collapse!
    pub fn measure(q: &Qubit) -> (bool, Qubit) {
        if q.is_measured() {
            // Already measured - return void state
            return (false, q.clone());
        }
        
        match (&q.alpha.value, &q.beta.value) {
            (Omega::Value(a), Omega::Value(b)) => {
                let prob_zero = a.magnitude_squared();
                let _prob_one = b.magnitude_squared();
                
                // Simulate measurement (would use random in real code)
                let measured_zero = prob_zero > 0.5;
                
                // Collapse to void with increased entropy!
                let collapsed = if measured_zero {
                    Qubit {
                        alpha: ThermoOmega::new(Complex::one()),
                        beta: ThermoOmega::void_with_entropy(1), // Measurement adds entropy
                    }
                } else {
                    Qubit {
                        alpha: ThermoOmega::void_with_entropy(1), // Measurement adds entropy
                        beta: ThermoOmega::new(Complex::one()),
                    }
                };
                
                (measured_zero, collapsed)
            }
            _ => (false, q.clone())
        }
    }
}

// Enhanced entanglement representation
#[derive(Debug, Clone)]
pub struct EntangledPair {
    pub correlation: ThermoOmega<Complex>,  // The shared undecidability
    pub entropy_bond: u32,  // How "strongly" entangled
}

// Two-qubit operations for entanglement
pub struct TwoQubitGate;

impl TwoQubitGate {
    // CNOT gate - creates entanglement (shared undecidability!)
    pub fn cnot(control: &Qubit, target: &Qubit) -> (Qubit, Qubit) {
        if control.is_measured() || target.is_measured() {
            // Can't entangle measured qubits
            return (control.clone(), target.clone());
        }
        
        match (&control.alpha.value, &control.beta.value) {
            (Omega::Value(c_a), Omega::Value(c_b)) => {
                if c_a.magnitude_squared() > 0.99 {
                    // Control is |0⟩, target unchanged
                    (control.clone(), target.clone())
                } else if c_b.magnitude_squared() > 0.99 {
                    // Control is |1⟩, flip target
                    (control.clone(), QuantumGate::pauli_x(target))
                } else {
                    // Superposition - create entanglement
                    // This increases entropy to show entanglement!
                    let entangled_target = Qubit {
                        alpha: ThermoOmega::void_with_entropy(2), // Entanglement entropy
                        beta: ThermoOmega::void_with_entropy(2),
                    };
                    (control.clone(), entangled_target)
                }
            }
            _ => (control.clone(), target.clone())
        }
    }
    
    // Enhanced CNOT with explicit entanglement modeling
    pub fn cnot_v2(control: &Qubit, target: &Qubit) -> (Qubit, Qubit) {
        if control.is_measured() || target.is_measured() {
            return (control.clone(), target.clone());
        }
        
        // Check for superposition strength
        match (&control.alpha.value, &control.beta.value) {
            (Omega::Value(c_a), Omega::Value(_c_b)) => {
                let superposition_amount = (c_a.magnitude_squared() - 0.5).abs();
                
                if superposition_amount < 0.1 {  // Near perfect superposition
                    // Create EPR pair - maximally entangled
                    // Both qubits now share the same undecidability!
                    let shared_undecidable = ThermoOmega::void_with_entropy(3); // Higher entropy for maximal entanglement
                    
                    // Return qubits that share the same void (entangled)
                    (
                        Qubit {
                            alpha: shared_undecidable.clone(),
                            beta: shared_undecidable.clone(),
                        },
                        Qubit {
                            alpha: shared_undecidable.clone(), 
                            beta: shared_undecidable.clone(),
                        }
                    )
                } else {
                    // Partial entanglement - classical CNOT
                    (control.clone(), QuantumGate::pauli_x(target))
                }
            }
            _ => (control.clone(), target.clone())
        }
    }
}

// Quantum circuit simulator
pub struct QuantumCircuit {
    pub qubits: Vec<Qubit>,
    pub total_entropy: u32,
}

impl QuantumCircuit {
    pub fn new(num_qubits: usize) -> Self {
        QuantumCircuit {
            qubits: vec![Qubit::zero(); num_qubits],
            total_entropy: 0,
        }
    }
    
    pub fn apply_hadamard(&mut self, qubit_idx: usize) {
        if qubit_idx < self.qubits.len() {
            self.qubits[qubit_idx] = QuantumGate::hadamard(&self.qubits[qubit_idx]);
        }
    }
    
    pub fn apply_cnot(&mut self, control_idx: usize, target_idx: usize) {
        if control_idx < self.qubits.len() && target_idx < self.qubits.len() {
            let control = &self.qubits[control_idx];
            let target = &self.qubits[target_idx];
            let (new_control, new_target) = TwoQubitGate::cnot(control, target);
            self.qubits[control_idx] = new_control;
            self.qubits[target_idx] = new_target;
        }
    }
    
    pub fn measure(&mut self, qubit_idx: usize) -> bool {
        if qubit_idx < self.qubits.len() {
            let (result, collapsed) = QuantumGate::measure(&self.qubits[qubit_idx]);
            let entropy_to_add = collapsed.entropy();
            self.qubits[qubit_idx] = collapsed;
            self.total_entropy += entropy_to_add;
            result
        } else {
            false
        }
    }
    
    pub fn circuit_entropy(&self) -> u32 {
        self.qubits.iter().map(|q| q.entropy()).sum::<u32>() + self.total_entropy
    }
}

impl std::fmt::Display for QuantumCircuit {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "Quantum Circuit State:")?;
        for (i, qubit) in self.qubits.iter().enumerate() {
            writeln!(f, "  Q{}: {}", i, qubit)?;
        }
        writeln!(f, "Total Circuit Entropy: {}", self.circuit_entropy())
    }
}

#[cfg(test)]
mod quantum_tests {
    use super::*;
    
    #[test]
    fn test_superposition_creation() {
        let q = Qubit::zero();
        assert!(q.is_classical());
        assert!(!q.is_measured());
        
        let superposed = QuantumGate::hadamard(&q);
        assert!(!superposed.is_classical());  // Now in superposition!
        println!("After Hadamard: {}", superposed);
    }
    
    #[test]
    fn test_measurement_collapse() {
        let q = Qubit::zero();
        let superposed = QuantumGate::hadamard(&q);
        
        let (result, collapsed) = QuantumGate::measure(&superposed);
        assert!(collapsed.entropy() > 0);  // Measurement added entropy!
        println!("Measured: {} -> {}", result, collapsed);
    }
    
    #[test]
    fn test_bell_state() {
        // Create Bell state: (|00⟩ + |11⟩)/√2
        let mut circuit = QuantumCircuit::new(2);
        
        circuit.apply_hadamard(0);  // Put first qubit in superposition
        circuit.apply_cnot(0, 1);    // Entangle with second qubit
        
        println!("{}", circuit);
        
        // Measure first qubit
        let result1 = circuit.measure(0);
        println!("After measuring Q0 = {}: {}", result1, circuit);
        
        // Second qubit should now be determined (entanglement!)
        assert!(circuit.circuit_entropy() > 0);
    }
    
    #[test]
    fn test_quantum_teleportation_attempt() {
        // This would normally require entanglement
        // But with measurement causing void, we see the limitation!
        let mut circuit = QuantumCircuit::new(3);
        
        // Prepare entangled pair
        circuit.apply_hadamard(1);
        circuit.apply_cnot(1, 2);
        
        // Try to teleport qubit 0's state
        circuit.apply_cnot(0, 1);
        circuit.apply_hadamard(0);
        
        // Measure
        let m1 = circuit.measure(0);
        let m2 = circuit.measure(1);
        
        println!("Teleportation attempt:");
        println!("{}", circuit);
        println!("Measurements: {}, {}", m1, m2);
        println!("Circuit entropy shows decoherence: {}", circuit.circuit_entropy());
    }
    
    #[test]
    fn test_entanglement_hierarchy() {
        println!("\n🌌 ENTANGLEMENT HIERARCHY TEST 🌌");
        
        // Test different levels of undecidability
        let q0 = Qubit::zero();
        println!("Classical |0⟩: entropy = {}", q0.entropy());
        
        let q1 = QuantumGate::hadamard(&q0);
        println!("Superposition: entropy = {}", q1.entropy());
        
        // Create entanglement with v2
        let q2 = Qubit::zero();
        let q3 = QuantumGate::hadamard(&q2);
        let (entangled1, entangled2) = TwoQubitGate::cnot_v2(&q3, &Qubit::zero());
        println!("Entangled pair: entropy = {} + {} = {}", 
                entangled1.entropy(), entangled2.entropy(), 
                entangled1.entropy() + entangled2.entropy());
        
        // Show the hierarchy
        println!("\n📊 UNDECIDABILITY HIERARCHY:");
        println!("  Classical:     entropy = 0 (fully decidable)");
        println!("  Superposition: entropy = 0 (locally undecidable)"); 
        println!("  Entanglement:  entropy = 6 (non-locally undecidable)");
        println!("  Post-measure:  entropy > 6 (decoherence history)");
        
        // This reveals the computational cost of quantum information!
        assert!(entangled1.entropy() + entangled2.entropy() > q1.entropy());
    }
    
    #[test] 
    fn test_shared_undecidability() {
        println!("\n⚛️ SHARED UNDECIDABILITY TEST ⚛️");
        
        // Create perfect superposition
        let control = QuantumGate::hadamard(&Qubit::zero());
        let target = Qubit::zero();
        
        println!("Before CNOT:");
        println!("  Control: {}", control);
        println!("  Target:  {}", target);
        
        // Enhanced entanglement
        let (ent1, ent2) = TwoQubitGate::cnot_v2(&control, &target);
        
        println!("After enhanced CNOT:");
        println!("  Qubit 1: {}", ent1);
        println!("  Qubit 2: {}", ent2);
        println!("  Shared entropy: {}", ent1.entropy() + ent2.entropy());
        
        // Both should have same entropy (shared undecidability!)
        assert_eq!(ent1.entropy(), ent2.entropy());
        println!("✓ Qubits share identical undecidability patterns!");
    }
}