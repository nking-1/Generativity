use omega_types::quantum::*;

fn main() {
    println!("🌌 Quantum Mechanics with Omega Types!");

    // Create a qubit in superposition
    let q = Qubit::zero();
    let superposed = QuantumGate::hadamard(&q);
    println!("Superposition: {}", superposed);

    // Try measurement
    let (result, collapsed) = QuantumGate::measure(&superposed);
    println!("Measured {} -> {}", result, collapsed);

    // Bell state experiment
    let mut circuit = QuantumCircuit::new(2);
    circuit.apply_hadamard(0);
    circuit.apply_cnot(0, 1);
    println!("\nBell State Circuit:");
    println!("{}", circuit);
}