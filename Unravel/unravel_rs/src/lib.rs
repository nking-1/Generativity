pub mod universe;
use crate::universe::*; 

// ==========================================
// 1. THE RESULT TYPE (Wheel)
// ==========================================

#[derive(Debug, Clone)]
pub enum UVal<T> {
    Valid(T),
    Infinity, // 1/0
    Nullity,  // 0/0
    Invalid(ParadoxPath), // Collapsed Entropy
}

// ==========================================
// 2. THE MONADIC CONTAINER
// ==========================================

pub struct Unravel<T> {
    pub result: UVal<T>,
    pub universe: Universe,
}

impl<T> Unravel<T> {
    pub fn new(val: T) -> Self {
        Unravel {
            result: UVal::Valid(val),
            universe: Universe::new(),
        }
    }

    pub fn from_parts(result: UVal<T>, universe: Universe) -> Self {
        Unravel { result, universe }
    }

    pub fn and_then<U, F>(self, f: F) -> Unravel<U> 
    where F: FnOnce(T) -> Unravel<U> 
    {
        let mut u = self.universe;
        u.time_step += 1;

        match self.result {
            UVal::Valid(val) => {
                let next = f(val);
                
                u.struct_entropy += next.universe.struct_entropy;
                u.time_entropy += next.universe.time_entropy;
                u.void_count += next.universe.void_count;
                u.mass += next.universe.mass;
                
                if next.universe.boundary_length > 0 {
                    let (new_bound, new_len) = append_hologram(
                        &u.boundary_value, u.boundary_length,
                        &next.universe.boundary_value, next.universe.boundary_length
                    );
                    u.boundary_value = new_bound;
                    u.boundary_length = new_len;
                }

                Unravel { result: next.result, universe: u }
            },
            UVal::Infinity => Unravel { result: UVal::Infinity, universe: u },
            UVal::Nullity => Unravel { result: UVal::Nullity, universe: u },
            
            UVal::Invalid(p) => {
                let new_path = ParadoxPath::SelfContradict(Box::new(p));
                Unravel { result: UVal::Invalid(new_path), universe: u }
            }
        }
    }
}

// ==========================================
// 3. PRIMITIVES
// ==========================================

pub fn crumble<T>(src: VoidSource) -> Unravel<T> {
    let path = ParadoxPath::BaseVeil(src);
    let (ds, dt) = path.rank();
    let tokens = path.flatten();
    let b_val = compress(&tokens);
    let b_len = tokens.len() as u64;
    
    let mut u = Universe::new();
    u.struct_entropy = ds;
    u.time_entropy = dt;
    u.void_count = 1;
    u.boundary_value = b_val;
    u.boundary_length = b_len;

    Unravel {
        result: UVal::Invalid(path),
        universe: u
    }
}

pub fn work(amount: u64) -> Unravel<()> {
    let mut u = Universe::new();
    u.mass = amount;
    Unravel { result: UVal::Valid(()), universe: u }
}

// ==========================================
// 4. THE SHIELD (Thermodynamic Observation)
// ==========================================

pub fn shield<T: Clone, F>(op: F, recover_val: T) -> Unravel<T>
where F: FnOnce() -> Unravel<T>
{
    let res = op();
    
    match res.result {
        UVal::Valid(v) => Unravel { result: UVal::Valid(v), universe: res.universe },
        
        UVal::Infinity => {
            let crash = crumble::<T>(VoidSource::LogicError("Collapsed Infinity".to_string()));
            let (final_bound, final_len) = append_hologram(
                &res.universe.boundary_value, res.universe.boundary_length,
                &crash.universe.boundary_value, crash.universe.boundary_length
            );
            
            let mut u = res.universe;
            u.struct_entropy += crash.universe.struct_entropy;
            u.time_entropy += crash.universe.time_entropy;
            u.void_count += 1;
            u.boundary_value = final_bound;
            u.boundary_length = final_len;
            
            Unravel { result: UVal::Valid(recover_val), universe: u }
        },
        
        UVal::Nullity => {
            let crash = crumble::<T>(VoidSource::LogicError("Collapsed Nullity".to_string()));
             let (final_bound, final_len) = append_hologram(
                &res.universe.boundary_value, res.universe.boundary_length,
                &crash.universe.boundary_value, crash.universe.boundary_length
            );
            let mut u = res.universe;
            u.struct_entropy += crash.universe.struct_entropy;
            u.time_entropy += crash.universe.time_entropy;
            u.void_count += 1;
            u.boundary_value = final_bound;
            u.boundary_length = final_len;

            Unravel { result: UVal::Valid(recover_val), universe: u }
        },
        
        UVal::Invalid(_) => {
             Unravel { result: UVal::Valid(recover_val), universe: res.universe }
        }
    }
}