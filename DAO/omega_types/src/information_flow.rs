// information_flow.rs - Dynamic systems and the I_max optimization principle

use crate::*;
use std::collections::HashMap;

// A dynamic system with bounded structure and perpetual change
#[derive(Debug, Clone)]
pub struct BoundedSystem {
    pub s_min: u32,          // Minimum structure
    pub s_max: u32,          // Maximum structure  
    pub structure: Vec<u32>, // Structure at each time step
    pub entropy_timeline: Vec<u32>,
}

impl BoundedSystem {
    pub fn new(s_min: u32, s_max: u32) -> Result<Self, String> {
        if s_min + 1 >= s_max {
            return Err("Need s_min + 1 < s_max for valid bounds".to_string());
        }
        
        Ok(BoundedSystem {
            s_min,
            s_max, 
            structure: vec![s_min + 1], // Start with minimal valid structure
            entropy_timeline: vec![0],
        })
    }
    
    // Current structure level
    pub fn current_structure(&self) -> u32 {
        *self.structure.last().unwrap_or(&(self.s_min + 1))
    }
    
    // Structure change (DS) between last two time steps
    pub fn delta_structure(&self) -> u32 {
        if self.structure.len() < 2 {
            return 0;
        }
        
        let current = self.structure[self.structure.len() - 1];
        let previous = self.structure[self.structure.len() - 2];
        
        if current > previous {
            current - previous
        } else {
            previous - current
        }
    }
    
    // Information flow I_val = S * DS
    pub fn information_flow(&self) -> u32 {
        self.current_structure() * self.delta_structure()
    }
    
    // Maximum possible DS given current S
    pub fn max_possible_delta(&self) -> u32 {
        let current = self.current_structure();
        let max_up = self.s_max - 1 - current;   // Can't exceed s_max - 1
        let max_down = current - self.s_min - 1; // Can't go below s_min + 1
        std::cmp::max(max_up, max_down)
    }
    
    // Evolve the system with perpetual change
    pub fn evolve(&mut self, direction: ChangeDirection) -> ThermoOmega<u32> {
        let current = self.current_structure();
        let time = self.structure.len();
        
        let new_structure = match direction {
            ChangeDirection::Increase(delta) => {
                let target = current + delta;
                if target < self.s_max {
                    target
                } else {
                    self.s_max - 1 // Clamp to maximum
                }
            }
            ChangeDirection::Decrease(delta) => {
                let target = if current > delta { current - delta } else { 0 };
                if target > self.s_min {
                    target
                } else {
                    self.s_min + 1 // Clamp to minimum
                }
            }
            ChangeDirection::Optimize => {
                // Try to maximize I_val = S * DS
                self.find_optimal_next_state()
            }
        };
        
        // Perpetual change: new structure must be different
        if new_structure == current {
            // Force change if we tried to stay the same
            if current < self.s_max - 1 {
                self.structure.push(current + 1);
            } else {
                self.structure.push(current - 1);
            }
        } else {
            self.structure.push(new_structure);
        }
        
        // Calculate entropy based on system complexity
        let entropy = self.calculate_system_entropy();
        self.entropy_timeline.push(entropy);
        
        ThermoOmega {
            value: Omega::Value(self.information_flow()),
            entropy,
        }
    }
    
    // Find the structure that maximizes I_val (but this is impossible at extremes!)
    fn find_optimal_next_state(&self) -> u32 {
        let current = self.current_structure();
        let mut best_structure = current + 1;
        let mut best_i_val = 0;
        
        // Try all valid next states
        for candidate in (self.s_min + 1)..(self.s_max) {
            if candidate != current { // Must change
                let delta = if candidate > current {
                    candidate - current
                } else {
                    current - candidate
                };
                let i_val = candidate * delta;
                
                if i_val > best_i_val {
                    best_i_val = i_val;
                    best_structure = candidate;
                }
            }
        }
        
        best_structure
    }
    
    fn calculate_system_entropy(&self) -> u32 {
        // Entropy based on:
        // 1. System complexity
        // 2. History of changes
        // 3. Distance from optimization
        
        let complexity_entropy = (self.current_structure() as f64).ln() as u32;
        let change_entropy = self.structure.len() as u32;
        let optimization_entropy = self.calculate_optimization_distance();
        
        complexity_entropy + change_entropy + optimization_entropy
    }
    
    fn calculate_optimization_distance(&self) -> u32 {
        // How far are we from the theoretical I_max?
        let current_i_val = self.information_flow();
        let theoretical_max = (self.s_max - 1) * (self.s_max - self.s_min - 1);
        
        if theoretical_max > current_i_val {
            (theoretical_max - current_i_val) / 10 // Scale down
        } else {
            0
        }
    }
    
    // Test the I_max impossibility theorem
    pub fn test_i_max_impossibility(&mut self) -> ThermoOmega<String> {
        println!("🎯 Testing I_max impossibility theorem...");
        
        // Try to achieve maximum S and maximum DS simultaneously
        let target_s = self.s_max - 1;
        let target_ds = self.s_max - self.s_min - 1;
        
        println!("  Target S: {}, Target DS: {}", target_s, target_ds);
        println!("  Theoretical I_max: {}", target_s * target_ds);
        
        // First, reach maximum structure
        while self.current_structure() < target_s {
            let result = self.evolve(ChangeDirection::Increase(1));
            if result.value.is_void() {
                return ThermoOmega {
                    value: Omega::Void,
                    entropy: result.entropy + 1,
                };
            }
        }
        
        println!("  Reached S = {}", self.current_structure());
        
        // Now try to achieve maximum DS
        let current_ds = self.delta_structure();
        println!("  Current DS = {}, Need DS = {}", current_ds, target_ds);
        
        if current_ds == target_ds {
            ThermoOmega {
                value: Omega::Value("IMPOSSIBLE: Achieved maximum S and DS!".to_string()),
                entropy: self.entropy_timeline.last().copied().unwrap_or(0) + 100,
            }
        } else {
            ThermoOmega {
                value: Omega::Value(format!(
                    "As predicted: Cannot achieve both max S ({}) and max DS ({}). Got DS = {}",
                    target_s, target_ds, current_ds
                )),
                entropy: self.entropy_timeline.last().copied().unwrap_or(0),
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum ChangeDirection {
    Increase(u32),
    Decrease(u32), 
    Optimize, // Try to maximize I_val
}

// Unbounded OmegaSystem that can grow without limit
#[derive(Debug, Clone)]
pub struct OmegaSystem {
    pub structure: Vec<u32>,
    pub growth_rate: f64,
    pub entropy_timeline: Vec<u32>,
}

impl OmegaSystem {
    pub fn new(initial_structure: u32, growth_rate: f64) -> Self {
        OmegaSystem {
            structure: vec![initial_structure],
            growth_rate,
            entropy_timeline: vec![0],
        }
    }
    
    pub fn current_structure(&self) -> u32 {
        *self.structure.last().unwrap_or(&1)
    }
    
    pub fn delta_structure(&self) -> u32 {
        if self.structure.len() < 2 {
            return 0;
        }
        
        let current = self.structure[self.structure.len() - 1];
        let previous = self.structure[self.structure.len() - 2];
        
        if current > previous {
            current - previous
        } else {
            previous - current
        }
    }
    
    pub fn information_flow(&self) -> u64 {
        (self.current_structure() as u64) * (self.delta_structure() as u64)
    }
    
    // Unbounded growth - can exceed any bound
    pub fn evolve(&mut self) -> ThermoOmega<u64> {
        let current = self.current_structure();
        let time = self.structure.len() as f64;
        
        // Exponential growth with chaotic changes
        let growth_factor = (time * self.growth_rate).exp();
        let chaotic_change = ((time * 7.0).sin() * 10.0) as u32;
        
        let new_structure = (current as f64 * growth_factor) as u32 + chaotic_change;
        
        self.structure.push(new_structure);
        
        // Omega systems have unbounded entropy growth
        let entropy = (time as u32) * 2 + self.information_flow() as u32 / 100;
        self.entropy_timeline.push(entropy);
        
        ThermoOmega {
            value: Omega::Value(self.information_flow()),
            entropy,
        }
    }
    
    // Demonstrate unbounded growth
    pub fn demonstrate_unbounded(&mut self, target: u64) -> ThermoOmega<bool> {
        println!("🌊 Demonstrating unbounded growth toward {}", target);
        
        let mut steps = 0;
        while self.information_flow() < target && steps < 50 {
            let result = self.evolve();
            steps += 1;
            
            if steps % 10 == 0 {
                println!("  Step {}: I_val = {}, S = {}", 
                         steps, self.information_flow(), self.current_structure());
            }
            
            if result.value.is_void() {
                return ThermoOmega {
                    value: Omega::Void,
                    entropy: result.entropy,
                };
            }
        }
        
        let reached_target = self.information_flow() >= target;
        println!("  Final: I_val = {}, Target reached: {}", 
                 self.information_flow(), reached_target);
        
        ThermoOmega {
            value: Omega::Value(reached_target),
            entropy: self.entropy_timeline.last().copied().unwrap_or(0),
        }
    }
}

// Information morphism between systems
#[derive(Debug, Clone)]
pub struct InfoMorphism {
    pub source_complexity: u32,
    pub target_complexity: u32,
    pub transformation_rate: u32,
}

impl InfoMorphism {
    pub fn new(source: u32, target: u32, rate: u32) -> Self {
        InfoMorphism {
            source_complexity: source,
            target_complexity: target,
            transformation_rate: rate.max(1), // Rate must be > 0
        }
    }
    
    pub fn information_flow(&self) -> u32 {
        self.source_complexity * self.transformation_rate
    }
    
    // Identity morphism
    pub fn identity(complexity: u32) -> Self {
        InfoMorphism {
            source_complexity: complexity,
            target_complexity: complexity,
            transformation_rate: 1,
        }
    }
    
    // Composition of morphisms
    pub fn compose(f: &InfoMorphism, g: &InfoMorphism) -> Option<InfoMorphism> {
        if f.target_complexity == g.source_complexity {
            Some(InfoMorphism {
                source_complexity: f.source_complexity,
                target_complexity: g.target_complexity,
                transformation_rate: f.transformation_rate + g.transformation_rate, // Simplified
            })
        } else {
            None
        }
    }
}

// Category of information systems with I_max constraints
pub struct InfoCategory {
    pub i_max_global: u32,
    pub objects: Vec<u32>, // Complexity levels
    pub morphisms: HashMap<(u32, u32), Vec<InfoMorphism>>,
}

impl InfoCategory {
    pub fn new(i_max: u32) -> Self {
        InfoCategory {
            i_max_global: i_max,
            objects: Vec::new(),
            morphisms: HashMap::new(),
        }
    }
    
    pub fn add_object(&mut self, complexity: u32) {
        if !self.objects.contains(&complexity) {
            self.objects.push(complexity);
            // Add identity morphism
            let id = InfoMorphism::identity(complexity);
            self.morphisms.entry((complexity, complexity))
                .or_insert_with(Vec::new)
                .push(id);
        }
    }
    
    pub fn add_morphism(&mut self, source: u32, target: u32, rate: u32) -> Result<(), String> {
        let morphism = InfoMorphism::new(source, target, rate);
        
        // Check I_max constraint
        if morphism.information_flow() > self.i_max_global {
            return Err(format!(
                "Morphism I_val {} exceeds global I_max {}", 
                morphism.information_flow(), 
                self.i_max_global
            ));
        }
        
        self.morphisms.entry((source, target))
            .or_insert_with(Vec::new)
            .push(morphism);
        
        Ok(())
    }
    
    // Find optimal morphism from source to target
    pub fn optimal_morphism(&self, source: u32, target: u32) -> Option<&InfoMorphism> {
        self.morphisms.get(&(source, target))?
            .iter()
            .max_by_key(|m| m.information_flow())
    }
    
    // Test the I_max constraint
    pub fn test_i_max_constraint(&self) -> ThermoOmega<String> {
        println!("🔍 Testing I_max constraints in category...");
        
        let mut violations = 0;
        let mut total_checked = 0;
        
        for ((source, target), morphisms) in &self.morphisms {
            for morphism in morphisms {
                total_checked += 1;
                if morphism.information_flow() > self.i_max_global {
                    violations += 1;
                    println!("  ❌ Violation: {} -> {} has I_val {} > I_max {}", 
                             source, target, morphism.information_flow(), self.i_max_global);
                }
            }
        }
        
        println!("  Checked {} morphisms, found {} violations", total_checked, violations);
        
        if violations == 0 {
            ThermoOmega {
                value: Omega::Value("All morphisms respect I_max constraint".to_string()),
                entropy: 0,
            }
        } else {
            ThermoOmega {
                value: Omega::Value(format!("Found {} I_max violations", violations)),
                entropy: violations,
            }
        }
    }
}

// Demonstrate the tracking limitation
pub struct TrackingExperiment;

impl TrackingExperiment {
    // Show bounded system cannot track unbounded omega system
    pub fn run_tracking_experiment(
        bounded_s_max: u32, 
        omega_growth_rate: f64
    ) -> ThermoOmega<String> {
        println!("\n🎭 TRACKING EXPERIMENT");
        println!("======================");
        println!("Bounded system (S_max = {}) trying to track unbounded OmegaSystem", bounded_s_max);
        
        let mut bounded = BoundedSystem::new(1, bounded_s_max).unwrap();
        let mut omega_sys = OmegaSystem::new(10, omega_growth_rate);
        
        let mut tracking_error = Vec::new();
        
        for step in 0..10 {
            // Evolve both systems
            let bounded_result = bounded.evolve(ChangeDirection::Optimize);
            let omega_result = omega_sys.evolve();
            
            // Calculate tracking error
            let bounded_i_val = bounded_result.value.unwrap_or(0) as u64;
            let omega_i_val = omega_result.value.unwrap_or(0);
            
            let error = if omega_i_val > bounded_i_val {
                omega_i_val - bounded_i_val
            } else {
                bounded_i_val - omega_i_val
            };
            
            tracking_error.push(error);
            
            println!("  Step {}: Bounded I_val = {}, Omega I_val = {}, Error = {}", 
                     step, bounded_i_val, omega_i_val, error);
        }
        
        // Analyze results
        let final_error = tracking_error.last().copied().unwrap_or(0);
        let total_entropy = bounded.entropy_timeline.last().copied().unwrap_or(0) +
                           omega_sys.entropy_timeline.last().copied().unwrap_or(0);
        
        if final_error > 1000 {
            ThermoOmega {
                value: Omega::Value(format!(
                    "✅ As predicted: Bounded system cannot track unbounded. Final error: {}", 
                    final_error
                )),
                entropy: total_entropy,
            }
        } else {
            ThermoOmega {
                value: Omega::Value(format!(
                    "❓ Unexpected: Bounded system kept pace. Final error: {}", 
                    final_error
                )),
                entropy: total_entropy + 10, // Unexpected result adds entropy
            }
        }
    }
}

// Connection to consciousness and observation
pub struct ObservationSystem {
    pub observer_complexity: u32,
    pub observed_system: BoundedSystem,
    pub observation_history: Vec<u32>,
    pub veil_encounters: u32, // Times we hit information limits
}

impl ObservationSystem {
    pub fn new(observer_complexity: u32, system: BoundedSystem) -> Self {
        ObservationSystem {
            observer_complexity,
            observed_system: system,
            observation_history: Vec::new(),
            veil_encounters: 0,
        }
    }
    
    // Observe the system - limited by observer complexity
    pub fn observe(&mut self) -> ThermoOmega<u32> {
        let actual_structure = self.observed_system.current_structure();
        
        // Observer can only perceive information up to their complexity
        let perceived_structure = if actual_structure > self.observer_complexity {
            // Hit an information veil!
            self.veil_encounters += 1;
            println!("  🎭 Information veil encountered! Actual: {}, Perceived: {}", 
                     actual_structure, self.observer_complexity);
            self.observer_complexity
        } else {
            actual_structure
        };
        
        self.observation_history.push(perceived_structure);
        
        // Entropy increases with veil encounters
        let entropy = self.observation_history.len() as u32 + self.veil_encounters * 3;
        
        ThermoOmega {
            value: Omega::Value(perceived_structure),
            entropy,
        }
    }
    
    // Evolution of the observation process
    pub fn observe_evolution(&mut self, steps: u32) -> ThermoOmega<String> {
        println!("\n👁️ OBSERVATION EVOLUTION");
        println!("========================");
        println!("Observer complexity: {}", self.observer_complexity);
        
        for step in 0..steps {
            // System evolves
            let system_result = self.observed_system.evolve(ChangeDirection::Optimize);
            
            // Observer tries to track it
            let observation_result = self.observe();
            
            if step % 3 == 0 {
                println!("  Step {}: System S = {}, Observed = {}, Veils hit = {}", 
                         step, 
                         self.observed_system.current_structure(),
                         observation_result.value.unwrap_or(0),
                         self.veil_encounters);
            }
        }
        
        let final_entropy = self.observation_history.len() as u32 + self.veil_encounters * 3;
        
        ThermoOmega {
            value: Omega::Value(format!(
                "Observation complete. {} veil encounters. Observer {} tracking system up to {}",
                self.veil_encounters,
                if self.veil_encounters > 0 { "partially" } else { "fully" },
                self.observed_system.current_structure()
            )),
            entropy: final_entropy,
        }
    }
}

#[cfg(test)]
mod information_flow_tests {
    use super::*;
    
    #[test]
    fn test_bounded_system_evolution() {
        println!("\n🔄 BOUNDED SYSTEM EVOLUTION TEST");
        
        let mut system = BoundedSystem::new(2, 10).unwrap();
        
        println!("System bounds: {} < S < {}", system.s_min, system.s_max);
        println!("Initial structure: {}", system.current_structure());
        
        for step in 0..5 {
            let result = system.evolve(ChangeDirection::Optimize);
            println!("  Step {}: S = {}, DS = {}, I_val = {}, entropy = {}", 
                     step, 
                     system.current_structure(),
                     system.delta_structure(),
                     result.value.unwrap_or(0),
                     result.entropy);
        }
    }
    
    #[test]
    fn test_i_max_impossibility() {
        println!("\n⚡ I_MAX IMPOSSIBILITY TEST");
        
        let mut system = BoundedSystem::new(1, 8).unwrap();
        let result = system.test_i_max_impossibility();
        
        println!("Result: {}", result.value.unwrap_or("VOID".to_string()));
        println!("Entropy: {}", result.entropy);
    }
    
    #[test]
    fn test_tracking_experiment() {
        println!("\n🎭 ALPHA-OMEGA TRACKING TEST");
        
        let result = TrackingExperiment::run_tracking_experiment(20, 0.1);
        println!("\nTracking result: {}", result.value.unwrap_or("VOID".to_string()));
        println!("Total entropy: {}", result.entropy);
    }
    
    #[test]
    fn test_observation_veils() {
        println!("\n👁️ OBSERVATION VEIL TEST");
        
        let system = BoundedSystem::new(1, 50).unwrap();
        let mut observer = ObservationSystem::new(15, system);
        
        let result = observer.observe_evolution(10);
        println!("Observation result: {}", result.value.unwrap_or("VOID".to_string()));
        println!("Observation entropy: {}", result.entropy);
    }
    
    #[test]
    fn test_info_category() {
        println!("\n📊 INFORMATION CATEGORY TEST");
        
        let mut category = InfoCategory::new(100); // I_max = 100
        
        // Add objects
        for complexity in [5, 10, 15, 20] {
            category.add_object(complexity);
        }
        
        // Add morphisms - some will violate I_max
        let _ = category.add_morphism(5, 10, 3);   // I_val = 15 ✓
        let _ = category.add_morphism(15, 20, 2);  // I_val = 30 ✓  
        let _ = category.add_morphism(20, 15, 10); // I_val = 200 ❌
        
        let result = category.test_i_max_constraint();
        println!("Category test: {}", result.value.unwrap_or("VOID".to_string()));
    }
}