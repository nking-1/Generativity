use unravel_rs::*;
use unravel_rs::universe::*;

fn safe_div(n: i32, d: i32) -> Unravel<i32> {
    if d == 0 {
        Unravel::from_parts(UVal::Infinity, Universe::new())
    } else {
        Unravel::new(n / d)
    }
}

fn main() {
    println!("🌌 Physics of Computation: Temporal vs Structural");
    println!("=================================================\n");

    // ---------------------------------------------------------
    // PART I: TEMPORAL ENTROPY (Monadic/Sequential)
    // ---------------------------------------------------------
    println!("📊 PART I: TEMPORAL ENTROPY (Sequential Causality)");
    println!("--------------------------------------------------\n");

    println!("🧪 Experiment 1a: Clean Sequential Chain");
    let temporal_clean = Unravel::new(100)
        .and_then(|x| Unravel::new(x / 2))
        .and_then(|x| Unravel::new(x - 10))
        .and_then(|x| Unravel::new(x * 3));
    print_report(&temporal_clean, "100 → /2 → -10 → ×3");

    println!("🧪 Experiment 1b: Sequential with Event Horizon");
    let temporal_event_horizon = shield(|| {
        Unravel::new(100)
            .and_then(|x| safe_div(x, 0))  // Singularity!
            .and_then(|x| Unravel::new(x + 999))  // Beyond horizon - won't execute
    }, 0);
    print_report(&temporal_event_horizon, "Event Horizon Test");

    // ---------------------------------------------------------
    // PART II: STRUCTURAL ENTROPY (Applicative/Parallel)
    // ---------------------------------------------------------
    println!("\n📊 PART II: STRUCTURAL ENTROPY (Parallel Branching)");
    println!("---------------------------------------------------\n");

    println!("🧪 Experiment 2a: Wheel Theory - Infinity Arithmetic");
    let inf_a = safe_div(100, 0);  // ∞
    let inf_b = safe_div(50, 0);   // ∞
    let wheel_result = entangle(inf_a, inf_b, |a, b| a + b);
    print_report(&wheel_result, "∞ + ∞ (Pure Wheel)");

    println!("🧪 Experiment 2b: Entangled Paradoxes");
    let crash_left = crumble::<i32>(VoidSource::LogicError("Left Timeline".to_string()));
    let crash_right = crumble::<i32>(VoidSource::LogicError("Right Timeline".to_string()));
    let entangled = entangle(crash_left, crash_right, |_, _| 42);
    print_report(&entangled, "Entangled Crashes");

    // ---------------------------------------------------------
    // PART III: MIXED REGIME (Temporal + Structural)
    // ---------------------------------------------------------
    println!("\n📊 PART III: MIXED REGIME (Sequential + Parallel)");
    println!("-------------------------------------------------\n");

    println!("🧪 Experiment 3: Branching Timeline with Singularities");
    
    // Create two parallel branches, each with sequential operations
    let branch_a = Unravel::new(100)
        .and_then(|x| safe_div(x, 2))
        .and_then(|x| safe_div(x, 0));  // Left singularity
    
    let branch_b = Unravel::new(200)
        .and_then(|x| safe_div(x, 4))
        .and_then(|x| safe_div(x, 0));  // Right singularity
    
    let mixed = entangle(branch_a, branch_b, |a, b| a + b);
    print_report(&mixed, "Parallel Timelines, Each with Singularity");

    // ---------------------------------------------------------
    // PART IV: QUANTUM COLLAPSE SIMULATION
    // ---------------------------------------------------------
    println!("\n📊 PART IV: QUANTUM COLLAPSE");
    println!("-----------------------------\n");

    println!("🧪 Experiment 4: Superposition → Measurement → Collapse");
    
    // Superposition: two parallel possible outcomes
    let state_spin_up = Unravel::new(1);
    let state_spin_down = Unravel::new(-1);
    
    let superposition = entangle(state_spin_up, state_spin_down, |up, down| {
        // In superposition - both states exist
        up + down  // Should be 0 (equal weights)
    });
    
    print_report(&superposition, "Superposition State");
    
    // Now "measure" by forcing collapse through shield
    let measured = shield(|| {
        entangle(
            safe_div(1, 0),  // Force collapse
            Unravel::new(-1),
            |_, down| down
        )
    }, -1);
    
    print_report(&measured, "Post-Measurement (Collapsed)");

    // ---------------------------------------------------------
    // PART V: STRESS TEST - Maximum Complexity
    // ---------------------------------------------------------
    println!("\n📊 PART V: MAXIMUM COMPLEXITY");
    println!("-----------------------------\n");

    println!("🧪 Experiment 5: Deeply Nested Parallel + Sequential");
    
    let complex = shield(|| {
        // Layer 1: Sequential chain
        Unravel::new(1000)
            .and_then(|x| {
                // Layer 2: Parallel branches
                let left = safe_div(x, 2).and_then(|y| safe_div(y, 0));
                let right = safe_div(x, 3).and_then(|y| safe_div(y, 0));
                
                entangle(left, right, |l, r| l + r)
            })
            .and_then(|result| {
                // Layer 3: Another sequential step after recombination
                Unravel::new(result * 2)
            })
    }, 0);
    
    print_report(&complex, "Nested (Sequential → Parallel → Sequential)");
}

fn print_report<T: std::fmt::Debug>(u: &Unravel<T>, name: &str) {
    println!("━━━ {} ━━━", name);
    
    match &u.result {
        UVal::Valid(v) => println!("📊 Result: {:?}", v),
        UVal::Infinity => println!("📊 Result: ∞ (Infinity)"),
        UVal::Nullity => println!("📊 Result: ⊥ (Nullity)"),
        UVal::Invalid(_) => println!("📊 Result: ⚠️  PARADOX"),
    }
    
    let univ = &u.universe;
    println!("⚡ Total Entropy: {}", univ.total_entropy());
    println!("   ├─ ⏰ Temporal:   {} (sequential causality)", univ.time_entropy);
    println!("   └─ 🌿 Structural: {} (parallel branching)", univ.struct_entropy);
    println!("⏱️  Time Steps: {}", univ.time_step);
    println!("⚛️  Mass: {}", univ.mass);
    println!("🌊 Void Encounters: {}", univ.void_count);
    
    println!("\n🕰️  CAUSAL HISTORY (from holographic boundary):");
    let history = reconstruct(&univ.boundary_value);
    
    if history.is_empty() {
        println!("   └─ [No paradoxes - clean vacuum]");
    } else {
        for (i, event) in history.iter().enumerate() {
            let marker = match event {
                ParadoxPath::BaseVeil(_) => "🔴",
                ParadoxPath::SelfContradict(_) => "⏩",
                ParadoxPath::Compose(_, _) => "🌿",
            };
            println!("   {} Event {}: {:?}", marker, i + 1, event);
        }
    }
    
    println!();
}