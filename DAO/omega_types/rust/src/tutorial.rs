// tutorial.rs - The Complete Omega Journey
// A tutorial that explores every feature through a space mission gone wrong

use crate::*;

pub fn run_tutorial() {
    println!("🚀 OMEGA TUTORIAL: Mission to the Void");
    println!("=====================================\n");
    
    // Chapter 1: Basic Omega - The Launch
    chapter_1_basics();
    
    // Chapter 2: Arithmetic and Propagation - Navigation
    chapter_2_arithmetic();
    
    // Chapter 3: Recovery Mechanisms - Emergency Protocols
    chapter_3_recovery();
    
    // Chapter 4: Thermodynamics - System Health
    chapter_4_thermodynamics();
    
    // Chapter 5: Conservation Laws - Noether's Theorem
    chapter_5_conservation();
    
    // Chapter 6: Practical Applications - Mission Control
    chapter_6_practical();
    
    // Chapter 7: The Complete Mission
    chapter_7_complete_mission();
}

fn chapter_1_basics() {
    println!("📖 Chapter 1: Basic Omega - The Launch");
    println!("--------------------------------------");
    
    // Creating Omega values
    let fuel = omega!(100);
    let empty = omega!();
    
    println!("Fuel level: {}", fuel);           // "100"
    println!("Empty tank: {}", empty);          // "⊥_ω"
    
    // Checking for void
    println!("Has fuel? {}", !fuel.is_void());   // true
    println!("Tank empty? {}", empty.is_void()); // true
    
    // Safe extraction with defaults
    let actual_fuel = fuel.unwrap_or(0);
    let phantom_fuel = empty.unwrap_or(0);
    println!("Actual fuel: {}", actual_fuel);   // 100
    println!("Phantom fuel: {}", phantom_fuel); // 0
    
    // Converting from Option
    let maybe_thrust: Option<i32> = Some(50);
    let thrust: Omega<i32> = maybe_thrust.into();
    println!("Thrust: {}", thrust);             // "50"
    
    let no_thrust: Option<i32> = None;
    let void_thrust: Omega<i32> = no_thrust.into();
    println!("No thrust: {}", void_thrust);     // "⊥_ω"
    
    println!();
}

fn chapter_2_arithmetic() {
    println!("📖 Chapter 2: Arithmetic - Navigation Calculations");
    println!("--------------------------------------------------");
    
    // Normal arithmetic
    let distance = omega!(1000);
    let speed = omega!(50);
    let time = distance.clone() / speed.clone();
    println!("Time to destination: {}", time);  // "20"
    
    // Division by zero - engine failure!
    let broken_speed = omega!(0);
    let infinite_time = distance.clone() / broken_speed;
    println!("Time with broken engine: {}", infinite_time); // "⊥_ω"
    
    // Void propagation - cascade failure
    let remaining = infinite_time.clone() - omega!(10);
    println!("Remaining after void: {}", remaining);        // "⊥_ω"
    
    // Modulo operations - orbital calculations
    let orbit = omega!(365);
    let phase = orbit % omega!(30);
    println!("Orbital phase: {}", phase);                   // "5"
    
    // Complex expressions with operators
    let trajectory = (omega!(100) + omega!(50)) * omega!(2) / omega!(5);
    println!("Trajectory calculation: {}", trajectory);      // "60"
    
    // The dangerous calculation that would panic in normal Rust
    let denominator = omega!(10) - omega!(10);  // Results in 0
    let dangerous = omega!(100) / denominator;
    println!("100 / (10-10) = {}", dangerous);              // "⊥_ω" (not panic!)
    
    println!();
}

fn chapter_3_recovery() {
    println!("📖 Chapter 3: Recovery - Emergency Protocols");
    println!("--------------------------------------------");
    
    // Simple recovery with 'or'
    let failed_sensor = omega!() ;
    let backup_reading = failed_sensor.or(42);
    println!("Sensor reading (recovered): {}", backup_reading); // "42"
    
    // Complex recovery with 'or_else'
    let primary_system: Omega<i32> = omega!();
    let recovered = primary_system.or_else(|| {
        println!("  [Activating backup system...]");
        omega!(999)
    });
    println!("System value: {}", recovered);                    // "999"
    
    // Pattern matching for different responses
    let critical_value = omega!(10) / omega!(0);
    let status = critical_value.match_omega(
        |v| format!("All systems go: {}", v),
        || format!("ALERT: System failure detected!")
    );
    println!("{}", status);
    
    // Chaining with 'then' - monadic style
    let chain_result = omega!(100)
        .then(|x| omega!(x / 10))    // 100 / 10 = 10
        .then(|x| omega!(x + 5))     // 10 + 5 = 15
        .then(|x| omega!(x * 2));    // 15 * 2 = 30
    println!("Chain result: {}", chain_result);                 // "30"
    
    // Chain with failure and recovery
    let failed_chain = omega!(100)
        .then(|x| omega!(x).divide(0))  // Fails here!
        .then(|x| omega!(x + 1000))     // Never executes
        .or(777);                        // Recovers
    println!("Failed chain (recovered): {}", failed_chain);     // "777"
    
    // Map transformation
    let celsius = omega!(100);
    let fahrenheit = celsius.map(|c| c * 9 / 5 + 32);
    println!("Temperature: {}°F", fahrenheit);                  // "212°F"
    
    println!();
}

fn chapter_4_thermodynamics() {
    println!("📖 Chapter 4: Thermodynamics - System Health Monitoring");
    println!("-------------------------------------------------------");
    
    // Clean operations have zero entropy
    let clean = thermo!(50).add(thermo!(30));
    println!("Clean calculation: {}", clean);  // "80 [entropy: 0]"
    
    // Errors increase entropy
    let error = thermo!(100).divide(thermo!(0));
    println!("Division by zero: {}", error);   // "⊥_ω [entropy: 1]"
    
    // Multiple errors accumulate entropy
    let multi_error = thermo!(10).divide(thermo!(0))  // +1 entropy
        .add(thermo!(20).divide(thermo!(0)));         // +2 more entropy
    println!("Multiple failures: {}", multi_error);    // "⊥_ω [entropy: 3]"
    
    // Recovery preserves entropy (conservation law!)
    let recovered = thermo!(100)
        .divide(thermo!(0))     // Fails, entropy: 1
        .recover(42);            // Recovers but keeps entropy
    println!("Recovered: {}", recovered);       // "42 [entropy: 1]"
    
    // Complex calculation with entropy tracking
    let mission_calc = thermo!(1000)
        .divide(thermo!(10))    // 1000/10 = 100, entropy: 0
        .add(thermo!(50))        // 100 + 50 = 150, entropy: 0
        .divide(thermo!(0))      // Fails! entropy: 1
        .add(thermo!(25))        // Void + 25 = void, entropy: 2
        .recover(200);           // Recovers to 200, entropy: 2
    
    println!("Mission calculation: {}", mission_calc);
    println!("  Health check: {} errors occurred", mission_calc.entropy());
    
    println!();
}

fn chapter_5_conservation() {
    println!("📖 Chapter 5: Conservation Laws - Noether's Theorem");
    println!("---------------------------------------------------");
    
    // Commutative operations preserve entropy
    let a = thermo!(5);
    let b = thermo!(3);
    let sum1 = a.clone().add(b.clone());
    let sum2 = b.clone().add(a.clone());
    
    println!("5 + 3 = {} (entropy: {})", sum1.value, sum1.entropy());
    println!("3 + 5 = {} (entropy: {})", sum2.value, sum2.entropy());
    assert_eq!(sum1.entropy(), sum2.entropy()); // Noether's theorem!
    
    // Even with errors, entropy is conserved under symmetry
    let error_a = thermo!(10).divide(thermo!(0));
    let normal_b = thermo!(5);
    
    let mix1 = error_a.clone().add(normal_b.clone());
    let mix2 = normal_b.add(error_a);
    
    println!("void + 5 entropy: {}", mix1.entropy());
    println!("5 + void entropy: {}", mix2.entropy());
    assert_eq!(mix1.entropy(), mix2.entropy()); // Still conserved!
    
    // Program refactoring preserves entropy
    // Original: (a + b) + c
    let original = thermo!(1).add(thermo!(2)).add(thermo!(3));
    // Refactored: a + (b + c)
    let refactored = thermo!(1).add(thermo!(2).add(thermo!(3)));
    
    println!("Original entropy: {}", original.entropy());
    println!("Refactored entropy: {}", refactored.entropy());
    assert_eq!(original.value, refactored.value);
    assert_eq!(original.entropy(), refactored.entropy());
    
    println!("✓ Conservation laws verified!\n");
}

fn chapter_6_practical() {
    println!("📖 Chapter 6: Practical Applications - Mission Control");
    println!("------------------------------------------------------");
    
    use crate::omega::practical::*;
    
    // Safe array access for sensor readings
    let sensors = vec![23.5, 24.1, 22.8, 23.9];
    let reading = safe_index(&sensors, 2);
    let bad_reading = safe_index(&sensors, 10);
    
    println!("Sensor 2: {}", reading.unwrap_or(0.0));        // 22.8
    println!("Sensor 10: {}", bad_reading.unwrap_or(0.0));   // 0.0 (default)
    
    // Safe square root for trajectory calculations
    let altitude = 10000.0;
    let good_sqrt = safe_sqrt(altitude);
    let impossible_sqrt = safe_sqrt(-100.0);
    
    println!("√10000 = {}", good_sqrt.unwrap_or(0.0));      // 100.0
    println!("√-100 = {}", impossible_sqrt.unwrap_or(0.0));  // 0.0 (void)
    
    // Database lookup for crew information
    let captain = lookup_user(1);
    let ghost = lookup_user(0);
    
    println!("Captain: {}", captain);    // "User_1 [entropy: 0]"
    println!("Ghost: {}", ghost);        // "⊥_ω [entropy: 1]"
    
    // Risk assessment with automatic recovery
    let risk1 = risk_assessment(10000, 6000, 20);
    println!("Normal risk: {}", risk1);  // "200 [entropy: 0]"
    
    let risk2 = risk_assessment(10000, 6000, 0);  // Division by zero!
    println!("Failed risk: {}", risk2);  // "50 [entropy: 2]"
    
    // Builder pattern for complex mission calculations
    let mission = ComputationBuilder::start(1000)
        .then_divide(10)    // Fuel calculation
        .then_add(50)       // Reserve fuel
        .then_divide(3)     // Per-engine distribution
        .recover_if_void(25) // Emergency minimum
        .build();
    
    println!("Mission fuel per engine: {}", mission);
    
    println!();
}

fn chapter_7_complete_mission() {
    println!("📖 Chapter 7: Complete Mission - Putting It All Together");
    println!("--------------------------------------------------------");
    
    // A complete space mission calculation with multiple failure points
    struct MissionData {
        fuel: ThermoOmega<i32>,
        distance: ThermoOmega<i32>,
        crew: ThermoOmega<i32>,
    }
    
    fn calculate_mission_viability(data: MissionData) -> String {
        // Calculate fuel per distance
        let fuel_efficiency = data.fuel.divide(data.distance);
        
        // Calculate resources per crew member
        let resources_per_person = thermo!(1000).divide(data.crew);
        
        // Combine factors
        let viability = fuel_efficiency
            .add(resources_per_person)
            .recover(0);
        
        // Generate report
        let health = match viability.entropy() {
            0 => "Perfect launch conditions ✓",
            1 => "Minor issues detected ⚠",
            2 => "Multiple failures - proceed with caution ⚠⚠",
            _ => "Critical failures - abort recommended ⚠⚠⚠",
        };
        
        format!(
            "Mission Viability Score: {}\nSystem Health: {}\nEntropy Level: {}",
            viability.value,
            health,
            viability.entropy()
        )
    }
    
    println!("Scenario 1: Normal Mission");
    println!("---------------------------");
    let normal_mission = MissionData {
        fuel: thermo!(1000),
        distance: thermo!(100),
        crew: thermo!(4),
    };
    println!("{}\n", calculate_mission_viability(normal_mission));
    
    println!("Scenario 2: Zero Distance (Stuck!)");
    println!("-----------------------------------");
    let stuck_mission = MissionData {
        fuel: thermo!(1000),
        distance: thermo!(0),  // Can't move!
        crew: thermo!(4),
    };
    println!("{}\n", calculate_mission_viability(stuck_mission));
    
    println!("Scenario 3: No Crew (Automated)");
    println!("--------------------------------");
    let auto_mission = MissionData {
        fuel: thermo!(1000),
        distance: thermo!(100),
        crew: thermo!(0),  // Unmanned!
    };
    println!("{}\n", calculate_mission_viability(auto_mission));
    
    // The grand finale: cascading calculations
    println!("🚀 FINAL MISSION CALCULATION");
    println!("============================");
    
    let grand_calculation = ComputationBuilder::start(50000)
        .then_divide(100)     // Stage 1: Initial burn
        .then_add(1000)       // Stage 2: Booster addition
        .then_divide(0)       // FAILURE: Engine malfunction!
        .recover_if_void(750) // Emergency protocols activate
        .build();
    
    println!("Final mission parameters: {}", grand_calculation);
    println!("Mission status: {}", 
        if grand_calculation.entropy() == 0 {
            "All systems nominal 🟢"
        } else {
            "Recovery protocols engaged 🟡"
        }
    );
    
    println!("\n========================================");
    println!("🎓 TUTORIAL COMPLETE!");
    println!("You've learned:");
    println!("  ✓ Total functions eliminate panics");
    println!("  ✓ Void (⊥_ω) represents impossibility");
    println!("  ✓ Entropy tracks computational health");
    println!("  ✓ Conservation laws govern transformations");
    println!("  ✓ Recovery preserves information");
    println!("  ✓ Everything computes, even through failure");
    println!("\n'From the void we came, through the void we compute!'");
}