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
    println!("🌌 Exploring the Void");
    println!("====================\n");

    // ---------------------------------------------------------
    // EXPERIMENT: Recursive Descent into Paradox
    // ---------------------------------------------------------
    println!("🧪 EXPERIMENT: Recursive Harmonic Series");
    println!("Computing sum of 100/(x-5) for x in [0..10]");
    println!("(Should hit singularity at x=5)\n");

    let result = shield(|| {
        let mut sum = Unravel::new(0);
        
        for x in 0..=10 {
            sum = sum.and_then(|acc| {
                let w = work(1); // Each iteration costs mass
                w.and_then(move |_| {
                    safe_div(100, x - 5).and_then(move |term| {
                        Unravel::new(acc + term)
                    })
                })
            });
        }
        
        sum
    }, 0);

    print_detailed_report(&result, "Harmonic Series with Singularity");

    // ---------------------------------------------------------
    // EXPERIMENT: Nested Paradox Composition
    // ---------------------------------------------------------
    println!("\n🧪 EXPERIMENT: Nested Paradox Composition");
    println!("Computing (100/a) / (50/b) where a=0, b=0\n");

    let nested_result = shield(|| {
        let step1 = safe_div(100, 0); // First infinity
        step1.and_then(|x| {
            let step2 = safe_div(50, 0); // Second infinity
            step2.and_then(move |y| {
                safe_div(x, y) // Infinity / Infinity = Nullity?
            })
        })
    }, -1);

    print_detailed_report(&nested_result, "Nested Infinities");

    // ---------------------------------------------------------
    // EXPERIMENT: Mass and Entropy Dance
    // ---------------------------------------------------------
    println!("\n🧪 EXPERIMENT: Mass-Entropy Interplay");
    println!("Heavy computation with intermittent singularities\n");

    let mass_result = shield(|| {
        work(100).and_then(|_| {
            safe_div(1000, 10).and_then(|x| {
                work(50).and_then(move |_| {
                    safe_div(x, 0).and_then(|y| { // Singularity mid-computation
                        work(25).and_then(move |_| {
                            Unravel::new(y * 2)
                        })
                    })
                })
            })
        })
    }, 0);

    print_detailed_report(&mass_result, "Mass-Entropy Dance");
}

fn print_detailed_report<T: std::fmt::Debug>(u: &Unravel<T>, name: &str) {
    println!("━━━ {} ━━━", name);
    
    match &u.result {
        UVal::Valid(v) => println!("📊 Result: {:?}", v),
        UVal::Infinity => println!("📊 Result: ∞"),
        UVal::Nullity => println!("📊 Result: ⊥ (Nullity)"),
        UVal::Invalid(_) => println!("📊 Result: PARADOX"),
    }
    
    let univ = &u.universe;
    println!("⚡ Total Entropy: {}", univ.total_entropy());
    println!("   └─ Temporal:    {}", univ.time_entropy);
    println!("   └─ Structural:  {}", univ.struct_entropy);
    println!("⏰ Time Steps: {}", univ.time_step);
    println!("⚛️  Mass: {}", univ.mass);
    println!("🌊 Void Encounters: {}", univ.void_count);
    println!("🔮 Boundary Length: {} tokens", univ.boundary_length);
    
    let sig_preview: String = univ.boundary_value.to_string()
        .chars()
        .take(40)
        .collect();
    println!("📡 Holographic Signature: {}...", sig_preview);
    
    // The time machine
    println!("\n🕰️  CAUSAL HISTORY (reconstructed from boundary):");
    let history = reconstruct(&univ.boundary_value);
    
    if history.is_empty() {
        println!("   └─ [Clean vacuum - no paradoxes encountered]");
    } else {
        for (i, event) in history.iter().enumerate() {
            println!("   {}. {:?}", i + 1, event);
        }
    }
    
    println!();
}