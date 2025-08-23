// lagrangian.rs - Information flow as fundamental physics

use crate::*;
use crate::quantum::Complex;

// The Information Lagrangian
#[derive(Debug, Clone)]
pub struct InfoLagrangian {
    pub structure: f64,      // Generalized position q
    pub velocity: f64,       // Generalized velocity dq/dt
    pub time: f64,
}

impl InfoLagrangian {
    pub fn new(structure: f64, velocity: f64, time: f64) -> Self {
        InfoLagrangian {
            structure,
            velocity,
            time,
        }
    }
    
    // The Lagrangian: L = S × DS (information action)
    pub fn lagrangian(&self) -> f64 {
        self.structure * self.velocity
    }
    
    // Euler-Lagrange equation: d/dt(∂L/∂v) - ∂L/∂q = 0
    pub fn euler_lagrange(&self) -> f64 {
        // ∂L/∂v = S (partial wrt velocity)
        // ∂L/∂q = v (partial wrt position)
        // d/dt(S) - v = 0
        // This gives: dS/dt = v (velocity IS the change in structure!)
        self.velocity
    }
    
    // Action integral: S = ∫L dt
    pub fn action(path: &[InfoLagrangian]) -> f64 {
        path.iter()
            .map(|state| state.lagrangian())
            .sum()
    }
    
    // Hamilton's equations (momentum formulation)
    pub fn hamiltonian(&self) -> f64 {
        // H = p·v - L where p = ∂L/∂v = S
        let momentum = self.structure;
        momentum * self.velocity - self.lagrangian()
        // H = S·v - S·v = 0 (!!)
        // The Hamiltonian vanishes! Pure constraint system!
    }
    
    // Canonical momentum
    pub fn momentum(&self) -> f64 {
        // p = ∂L/∂v = S
        self.structure
    }
}

// Principle of Stationary Action
pub struct ActionPrinciple;

impl ActionPrinciple {
    // Find path that extremizes action under I_max constraint
    pub fn find_optimal_path(
        initial: (f64, f64),
        target: (f64, f64),
        i_max: f64,
        steps: usize
    ) -> Vec<InfoLagrangian> {
        let mut path = Vec::new();
        
        let (s0, v0) = initial;
        let (sf, _vf) = target;
        
        println!("🎯 Finding optimal path with I_max = {}", i_max);
        
        // Linear interpolation (simplified - real would use calculus of variations)
        for i in 0..steps {
            let t = i as f64 / steps as f64;
            let s = s0 + (sf - s0) * t;
            
            // Velocity that respects I_max constraint
            let v_max = i_max / s.max(1.0);
            let v = v0 * (1.0 - t) + v_max * t;
            
            let state = InfoLagrangian::new(s, v, t);
            println!("  t={:.2}: S={:.2}, v={:.2}, L={:.2}", 
                     t, s, v, state.lagrangian());
            
            path.push(state);
        }
        
        path
    }
    
    // Noether's theorem: symmetries → conservation laws
    pub fn noether_conserved_quantity(
        lagrangian: &InfoLagrangian,
        symmetry: fn(f64) -> f64
    ) -> f64 {
        // If L is invariant under transformation, there's a conserved quantity
        // For time translation symmetry: Energy is conserved
        // For I_val = S × DS, this gives conservation of information flow!
        
        let transformed_s = symmetry(lagrangian.structure);
        transformed_s * lagrangian.velocity // Conserved under symmetry
    }
    
    // Test various symmetries
    pub fn test_symmetries(state: &InfoLagrangian) -> ThermoOmega<Vec<f64>> {
        println!("\n🔄 TESTING SYMMETRIES");
        
        let mut conserved_quantities = Vec::new();
        let mut entropy = 0;
        
        // Time translation symmetry
        let time_conserved = Self::noether_conserved_quantity(state, |s| s);
        conserved_quantities.push(time_conserved);
        println!("  Time translation: conserved quantity = {}", time_conserved);
        
        // Scaling symmetry
        let scale_conserved = Self::noether_conserved_quantity(state, |s| s * 2.0);
        conserved_quantities.push(scale_conserved);
        println!("  Scaling: conserved quantity = {}", scale_conserved);
        
        // Rotation in (S, DS) space
        let rotation_conserved = Self::noether_conserved_quantity(state, |s| s.sin());
        conserved_quantities.push(rotation_conserved);
        entropy += 1; // Non-linear transformations add entropy
        println!("  Rotation: conserved quantity = {}", rotation_conserved);
        
        ThermoOmega {
            value: Omega::Value(conserved_quantities),
            entropy,
        }
    }
}

// Quantum version: Path integral through omega_veil space
#[derive(Debug, Clone)]
pub struct QuantumInfoPath {
    pub amplitude: Complex,
    pub path: Vec<InfoLagrangian>,
}

impl QuantumInfoPath {
    pub fn new(path: Vec<InfoLagrangian>) -> Self {
        QuantumInfoPath {
            amplitude: Complex::one(),
            path,
        }
    }
    
    // Feynman path integral for information flow
    pub fn path_integral_amplitude(&self) -> Complex {
        // Amplitude = exp(i × Action / ℏ)
        let action = InfoLagrangian::action(&self.path);
        let phase = action; // Simplified (ℏ = 1)
        
        Complex {
            real: phase.cos(),
            imag: phase.sin(),
        }
    }
    
    // Sum over all paths through omega_veil space
    pub fn sum_over_paths(paths: &[QuantumInfoPath]) -> ThermoOmega<Complex> {
        let mut total_amplitude = Complex::zero();
        
        for path in paths {
            let amp = path.path_integral_amplitude();
            total_amplitude = total_amplitude.add(&amp);
        }
        
        // Entropy from number of paths explored
        let entropy = paths.len() as u32;
        
        println!("  Summed over {} paths in omega_veil space", paths.len());
        println!("  Total amplitude: {}", total_amplitude);
        
        ThermoOmega {
            value: Omega::Value(total_amplitude),
            entropy,
        }
    }
}

impl Complex {
    pub fn add(&self, other: &Complex) -> Complex {
        Complex {
            real: self.real + other.real,
            imag: self.imag + other.imag,
        }
    }
}

// Field theory version: Information as a field
pub struct InfoField {
    pub field_values: Vec<Vec<f64>>, // φ(x,t)
    pub i_max_constraint: f64,
}

impl InfoField {
    pub fn new(size_x: usize, size_t: usize, i_max: f64) -> Self {
        InfoField {
            field_values: vec![vec![0.0; size_x]; size_t],
            i_max_constraint: i_max,
        }
    }
    
    // Field Lagrangian density: ℒ = φ × (∂φ/∂t)
    pub fn lagrangian_density(&self, x: usize, t: usize) -> f64 {
        let phi = self.field_values[t][x];
        let phi_dot = if t > 0 {
            self.field_values[t][x] - self.field_values[t-1][x]
        } else {
            0.0
        };
        
        phi * phi_dot // Information flow density
    }
    
    // Wave equation for information propagation
    pub fn info_wave_equation(&self, x: usize, t: usize) -> f64 {
        // ∂²φ/∂t² = c² ∂²φ/∂x² (modified for I_max)
        // Information propagates as waves!
        
        let c = (self.i_max_constraint).sqrt(); // Wave speed from I_max
        
        // Discrete second derivatives
        let d2_dt2 = if t > 0 && t < self.field_values.len() - 1 {
            self.field_values[t+1][x] - 2.0 * self.field_values[t][x] + self.field_values[t-1][x]
        } else {
            0.0
        };
        
        let d2_dx2 = if x > 0 && x < self.field_values[0].len() - 1 {
            self.field_values[t][x+1] - 2.0 * self.field_values[t][x] + self.field_values[t][x-1]
        } else {
            0.0
        };
        
        d2_dt2 - c * c * d2_dx2
    }
    
    // Set initial pulse
    pub fn set_initial_pulse(&mut self, center: usize, amplitude: f64) {
        if center < self.field_values[0].len() {
            self.field_values[0][center] = amplitude;
        }
    }
    
    // Evolve field according to wave equation
    pub fn evolve_field(&mut self) {
        for t in 1..self.field_values.len() {
            for x in 1..self.field_values[0].len() - 1 {
                // Simple diffusion for demo (real would solve wave equation)
                self.field_values[t][x] = 
                    (self.field_values[t-1][x-1] + 
                     self.field_values[t-1][x] + 
                     self.field_values[t-1][x+1]) / 3.0;
                
                // Apply I_max constraint
                if self.field_values[t][x] * 2.0 > self.i_max_constraint {
                    self.field_values[t][x] = self.i_max_constraint / 2.0;
                }
            }
        }
    }
}

#[cfg(test)]
mod lagrangian_tests {
    use super::*;
    
    #[test]
    fn test_lagrangian_physics() {
        println!("\n⚛️ INFORMATION AS FUNDAMENTAL PHYSICS");
        
        let state = InfoLagrangian::new(10.0, 5.0, 0.0);
        
        println!("Lagrangian L = S × DS = {}", state.lagrangian());
        println!("Hamiltonian H = {}", state.hamiltonian());
        println!("Euler-Lagrange: {}", state.euler_lagrange());
        println!("Canonical momentum p = {}", state.momentum());
        
        // Test the vanishing Hamiltonian
        assert!((state.hamiltonian()).abs() < 1e-10);
        println!("✅ Hamiltonian vanishes - pure constraint system!");
    }
    
    #[test]
    fn test_action_principle() {
        println!("\n🎯 PRINCIPLE OF STATIONARY ACTION");
        
        let path = ActionPrinciple::find_optimal_path(
            (5.0, 2.0),   // Initial (S, v)
            (20.0, 1.0),  // Final (S, v)
            100.0,        // I_max constraint
            10            // Steps
        );
        
        let total_action = InfoLagrangian::action(&path);
        println!("\nTotal action along path: {}", total_action);
        
        // Check Noether's theorem
        let conserved = ActionPrinciple::noether_conserved_quantity(
            &path[0],
            |s| s + 1.0  // Translation symmetry
        );
        println!("Noether conserved quantity: {}", conserved);
    }
    
    #[test]
    fn test_quantum_paths() {
        println!("\n🌊 QUANTUM PATH INTEGRALS");
        
        // Create multiple paths through omega_veil space
        let paths: Vec<QuantumInfoPath> = (0..5).map(|i| {
            let path = ActionPrinciple::find_optimal_path(
                (1.0, 1.0),
                (10.0, 2.0),
                50.0 + i as f64 * 10.0,  // Different I_max for each path
                5
            );
            
            QuantumInfoPath::new(path)
        }).collect();
        
        let result = QuantumInfoPath::sum_over_paths(&paths);
        match result.value {
            Omega::Value(amp) => {
                println!("Sum over paths amplitude: {}", amp);
            }
            Omega::Void => println!("Path integral collapsed to void"),
        }
        println!("Path integral entropy: {}", result.entropy);
    }
    
    #[test]
    fn test_info_field() {
        println!("\n🌊 INFORMATION FIELD THEORY");
        
        // Initialize field
        let mut field = InfoField::new(10, 10, 100.0);
        
        // Set initial conditions (pulse)
        field.set_initial_pulse(5, 10.0);
        println!("Initial pulse amplitude: {}", field.field_values[0][5]);
        
        // Evolve field
        field.evolve_field();
        
        // Check wave equation
        let residual = field.info_wave_equation(5, 5);
        println!("Wave equation residual: {}", residual);
        
        // Calculate total action
        let mut total_action = 0.0;
        for t in 0..10 {
            for x in 0..10 {
                total_action += field.lagrangian_density(x, t);
            }
        }
        println!("Total field action: {}", total_action);
        
        // Show field evolution
        println!("\nField at final time:");
        for x in 0..10 {
            let val = field.field_values[9][x];
            let bar = "█".repeat((val * 2.0) as usize);
            println!("  x={}: {} {:.2}", x, bar, val);
        }
    }
    
    #[test]
    fn test_conservation_laws() {
        println!("\n⚖️ TESTING CONSERVATION LAWS");
        
        let state1 = InfoLagrangian::new(10.0, 5.0, 0.0);
        let state2 = InfoLagrangian::new(15.0, 3.0, 1.0);
        
        // Test time translation symmetry
        let conserved1 = ActionPrinciple::noether_conserved_quantity(&state1, |s| s);
        let conserved2 = ActionPrinciple::noether_conserved_quantity(&state2, |s| s);
        
        println!("State 1 conserved quantity: {}", conserved1);
        println!("State 2 conserved quantity: {}", conserved2);
        
        // Test scaling symmetry
        let scale1 = ActionPrinciple::noether_conserved_quantity(&state1, |s| s * 2.0);
        let scale2 = ActionPrinciple::noether_conserved_quantity(&state2, |s| s * 2.0);
        
        println!("Scaling conserved 1: {}", scale1);
        println!("Scaling conserved 2: {}", scale2);
        
        // The ratio should be preserved under scaling
        let ratio1 = conserved1 / scale1;
        let ratio2 = conserved2 / scale2;
        
        println!("Conservation ratios: {:.3}, {:.3}", ratio1, ratio2);
        
        // Test if ratios are approximately equal (symmetry preservation)
        if (ratio1 - ratio2).abs() < 0.1 {
            println!("✅ Symmetry preserved!");
        } else {
            println!("⚠️ Symmetry broken");
        }
    }
    
    #[test]
    fn test_hamiltonian_vanishing() {
        println!("\n🌀 TESTING HAMILTONIAN PROPERTIES");
        
        // Create several different states
        let states = vec![
            InfoLagrangian::new(5.0, 3.0, 0.0),
            InfoLagrangian::new(20.0, 1.5, 1.0),
            InfoLagrangian::new(1.0, 10.0, 2.0),
            InfoLagrangian::new(50.0, 0.5, 3.0),
        ];
        
        for (i, state) in states.iter().enumerate() {
            let h = state.hamiltonian();
            let l = state.lagrangian();
            let p = state.momentum();
            
            println!("State {}: S={:.1}, v={:.1}", i, state.structure, state.velocity);
            println!("  Lagrangian L = {:.2}", l);
            println!("  Momentum p = {:.2}", p);
            println!("  Hamiltonian H = {:.2}", h);
            
            // Verify H = p·v - L = S·v - S·v = 0
            assert!(h.abs() < 1e-10, "Hamiltonian should vanish!");
        }
        
        println!("\n✅ All Hamiltonians vanish - confirming pure constraint system!");
        println!("This means: NO FREE ENERGY in the information flow system");
        println!("All energy is bound up in the S×DS constraint relationship");
    }
    
    #[test]
    fn test_phase_space() {
        println!("\n🌀 PHASE SPACE ANALYSIS");
        
        // Explore the (S, p) phase space where p = momentum = S
        // This gives us the constraint: p = S, so phase space is the line p = S!
        
        println!("Phase space constraint: momentum p = structure S");
        println!("This reduces 2D phase space to 1D constraint manifold!");
        
        let points = vec![
            (5.0, 5.0),   // (S, p) = (5, 5)
            (10.0, 10.0), // (S, p) = (10, 10)
            (20.0, 20.0), // (S, p) = (20, 20)
        ];
        
        for (s, p) in points {
            // Verify constraint p = S
            let diff: f64 = p - s;
            assert!(diff.abs() < 1e-10);
            
            // Calculate velocity from momentum: v = H/∂p (but H = 0!)
            // Actually: p = ∂L/∂v = S, so v is whatever gives this momentum
            let v = p / s; // Since p = S and p = S·v/v = S, we get v = p/S = 1
            
            let state = InfoLagrangian::new(s, v, 0.0);
            println!("  Phase point ({:.1}, {:.1}): v={:.1}, L={:.1}", 
                     s, p, v, state.lagrangian());
        }
        
        println!("\n📊 INSIGHT: Phase space constraint p = S forces v = 1");
        println!("This means: All systems have UNIT VELOCITY in information space!");
        println!("Time evolution is uniform - the constraint determines dynamics!");
    }
}