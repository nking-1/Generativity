use unravel_rs::*; 
use unravel_rs::universe::*; 

// A Helper to make division look like an operator
fn safe_div(n: i32, d: i32) -> Unravel<i32> {
    if d == 0 {
        // Return Infinity (Valid in Wheel Theory)
        Unravel::from_parts(UVal::Infinity, Universe::new())
    } else {
        Unravel::new(n / d)
    }
}

fn main() {
    println!("🦀 Unravel Rust Crate v0.1");
    println!("===========================");

    // ---------------------------------------------------------
    // EXPERIMENT 1: The Single Singularity
    // ---------------------------------------------------------
    println!("\n🧪 EXPERIMENT 1: The Singularity");
    
    let computation = || {
        let w = work(10); 
        w.and_then(|_| safe_div(100, 0))
    };

    let safe_result = shield(computation, 0);
    print_report(&safe_result, "Single 1/0");


    // ---------------------------------------------------------
    // EXPERIMENT 2: The Vector Stress Test (Structural Entropy)
    // ---------------------------------------------------------
    println!("\n🧪 EXPERIMENT 2: Vector Stress");
    
    let inputs = vec![10, 5, 0, 2, 0]; // Two singularities
    
    let mut total_result = Unravel::new(Vec::new());
    
    for x in inputs {
        let item_result = shield(|| safe_div(100, x), 0);
        
        total_result = total_result.and_then(|mut vec| {
            Unravel {
                result: match item_result.result {
                    UVal::Valid(v) => { vec.push(v); UVal::Valid(vec) },
                    _ => UVal::Valid(vec) 
                },
                universe: item_result.universe 
            }
        });
    }
    
    print_report(&total_result, "Vector [10, 5, 0, 2, 0]");

    // ---------------------------------------------------------
    // EXPERIMENT 4: The Missing Physics (Unshielded Composition)
    // ---------------------------------------------------------
    println!("\n🧪 EXPERIMENT 4: Unshielded Composition");
    println!("We combine two Infinities WITHOUT shielding.");
    println!("Expected: Wheel Logic handles it (Inf + Inf = Inf), No Entropy.");
    
    let val_a = safe_div(100, 0); // Infinity
    let val_b = safe_div(50, 0);  // Infinity
    
    // We use 'entangle' (Applicative) to combine them
    // This mimics: (+) <$> (100/0) <*> (50/0)
    let result = entangle(val_a, val_b, |a, b| a + b);
    
    print_report(&result, "Inf + Inf (Wheel Theory)");
    
    
    // ---------------------------------------------------------
    // EXPERIMENT 5: Structural Entropy
    // ---------------------------------------------------------
    println!("\n🧪 EXPERIMENT 5: Structural Entropy");
    println!("We force two CRASHES and entangle them.");
    
    let crash_a = crumble::<i32>(VoidSource::LogicError("Left Branch".to_string()));
    let crash_b = crumble::<i32>(VoidSource::LogicError("Right Branch".to_string()));
    
    let struct_result = entangle(crash_a, crash_b, |a, b| a + b);
    
    print_report(&struct_result, "Entangled Crashes");
}

fn print_report<T: std::fmt::Debug>(u: &Unravel<T>, name: &str) {
    println!("--- Report: {} ---", name);
    match &u.result {
        UVal::Valid(v) => println!("   Result:  {:?}", v),
        _ => println!("   Result:  INVALID"),
    }
    
    let univ = &u.universe;
    println!("   Entropy: {} (Time={}, Struct={})", univ.total_entropy(), univ.time_entropy, univ.struct_entropy);
    println!("   Mass:    {}", univ.mass);
    println!("   Sig:     {}...", univ.boundary_value.to_string().chars().take(20).collect::<String>());
    
    // RECONSTRUCTION (The Time Machine)
    println!("\n   🕰️  RECONSTRUCTED HISTORY:");
    let history = reconstruct(&univ.boundary_value);
    if history.is_empty() {
        println!("      (Clean Vacuum)");
    } else {
        for (i, event) in history.iter().enumerate() {
             println!("      {}. {:?}", i + 1, event);
        }
    }
    println!("");
}