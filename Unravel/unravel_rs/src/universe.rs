use num_bigint::BigInt;
use num_traits::{Zero, ToPrimitive};
use num_integer::Integer;

// ==========================================
// 1. ONTOLOGY
// ==========================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum VoidSource {
    DivByZero,
    LogicError(String),
    RootEntropy,
    VoidNeutral,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParadoxPath {
    BaseVeil(VoidSource),
    SelfContradict(Box<ParadoxPath>),      // Next/Time
    Compose(Box<ParadoxPath>, Box<ParadoxPath>), // Mix/Structure
}

// ... (Universe struct remains the same) ...
#[derive(Debug, Clone)]
pub struct Universe {
    pub struct_entropy: u64,
    pub time_entropy: u64,
    pub time_step: u64,
    pub void_count: u64,
    pub mass: u64,
    pub boundary_value: BigInt,
    pub boundary_length: u64,
}

impl Universe {
    pub fn new() -> Self {
        Universe {
            struct_entropy: 0,
            time_entropy: 0,
            time_step: 0,
            void_count: 0,
            mass: 0,
            boundary_value: BigInt::zero(),
            boundary_length: 0,
        }
    }

    pub fn total_entropy(&self) -> u64 {
        self.struct_entropy + self.time_entropy
    }
}

// ==========================================
// 2. HOLOGRAPHY (Gödel Encoding)
// ==========================================

const BASE: u64 = 256;

// Tokens
const T_DIV_ZERO: u64 = 1;
const T_ROOT: u64 = 2;
const T_SEQ: u64 = 10;
const T_MIX_OPEN: u64 = 20;
const T_MIX_MID: u64 = 21;
const T_MIX_CLOSE: u64 = 22;
const T_MSG_OPEN: u64 = 30;
const T_MSG_CLOSE: u64 = 31;

// ... (ParadoxPath implementation remains the same) ...
impl ParadoxPath {
    pub fn rank(&self) -> (u64, u64) {
        match self {
            ParadoxPath::BaseVeil(VoidSource::VoidNeutral) => (0, 0),
            ParadoxPath::BaseVeil(_) => (0, 1),
            ParadoxPath::SelfContradict(p) => {
                let (s, t) = p.rank();
                (s, t + 1)
            }
            ParadoxPath::Compose(p1, p2) => {
                let (s1, t1) = p1.rank();
                let (s2, t2) = p2.rank();
                (s1 + s2 + 1, t1 + t2)
            }
        }
    }

    pub fn flatten(&self) -> Vec<u64> {
        match self {
            ParadoxPath::BaseVeil(src) => match src {
                VoidSource::VoidNeutral => vec![],
                VoidSource::DivByZero => vec![T_DIV_ZERO],
                VoidSource::RootEntropy => vec![T_ROOT],
                VoidSource::LogicError(msg) => {
                    let mut v = vec![T_MSG_OPEN];
                    v.extend(msg.bytes().map(|b| b as u64));
                    v.push(T_MSG_CLOSE);
                    v
                }
            },
            ParadoxPath::SelfContradict(p) => {
                let mut v = vec![T_SEQ];
                v.extend(p.flatten());
                v
            },
            ParadoxPath::Compose(p1, p2) => {
                let mut v = vec![T_MIX_OPEN];
                v.extend(p1.flatten());
                v.push(T_MIX_MID);
                v.extend(p2.flatten());
                v.push(T_MIX_CLOSE);
                v
            }
        }
    }
}

pub fn compress(tokens: &[u64]) -> BigInt {
    let mut res = BigInt::zero();
    let base = BigInt::from(BASE);
    for &token in tokens.iter().rev() {
        res = res * &base + BigInt::from(token);
    }
    res
}

pub fn append_hologram(val_old: &BigInt, len_old: u64, val_new: &BigInt, len_new: u64) -> (BigInt, u64) {
    let base = BigInt::from(BASE);
    // Shift val_new to high bits, keep val_old in low bits (Chronological)
    let shift = base.pow(len_old as u32);
    let new_val = val_old + (val_new * shift);
    (new_val, len_old + len_new)
}

pub fn decompress(mut n: BigInt) -> Vec<u64> {
    let mut tokens = Vec::new();
    let base = BigInt::from(BASE);
    while n > BigInt::zero() {
        let (rest, digit) = n.div_rem(&base);
        tokens.push(digit.to_u64().unwrap_or(0));
        n = rest;
    }
    tokens // Returns [Old ... New]
}

// NEW: The Recursive Descent Parser
fn parse_path(tokens: &[u64]) -> Option<(ParadoxPath, &[u64])> {
    if tokens.is_empty() { return None; }
    
    let (head, rest) = tokens.split_first()?;
    
    match *head {
        T_DIV_ZERO => Some((ParadoxPath::BaseVeil(VoidSource::DivByZero), rest)),
        T_ROOT => Some((ParadoxPath::BaseVeil(VoidSource::RootEntropy), rest)),
        
        // String Parsing
        T_MSG_OPEN => {
            let mut end_idx = 0;
            let mut found = false;
            for (i, &t) in rest.iter().enumerate() {
                if t == T_MSG_CLOSE {
                    end_idx = i;
                    found = true;
                    break;
                }
            }
            
            if found {
                let bytes: Vec<u8> = rest[..end_idx].iter().map(|&x| x as u8).collect();
                let msg = String::from_utf8(bytes).unwrap_or("Invalid UTF8".to_string());
                let remaining = &rest[end_idx + 1..]; // Skip the CLOSE token
                Some((ParadoxPath::BaseVeil(VoidSource::LogicError(msg)), remaining))
            } else {
                None
            }
        },
        
        T_SEQ => {
            let (p, remaining) = parse_path(rest)?;
            Some((ParadoxPath::SelfContradict(Box::new(p)), remaining))
        },
        
        T_MIX_OPEN => {
            let (p1, rem1) = parse_path(rest)?;
            if rem1.is_empty() || rem1[0] != T_MIX_MID { return None; }
            let (p2, rem2) = parse_path(&rem1[1..])?; // Skip MID
            if rem2.is_empty() || rem2[0] != T_MIX_CLOSE { return None; }
            Some((ParadoxPath::Compose(Box::new(p1), Box::new(p2)), &rem2[1..])) // Skip CLOSE
        },
        
        _ => None
    }
}

// UPDATED: Returns actual Objects
pub fn reconstruct(n: &BigInt) -> Vec<ParadoxPath> {
    let tokens = decompress(n.clone());
    let mut events = Vec::new();
    let mut slice = tokens.as_slice();
    
    while !slice.is_empty() {
        match parse_path(slice) {
            Some((p, rest)) => {
                events.push(p);
                slice = rest;
            },
            None => break, // Stop if we hit garbage or alignment errors
        }
    }
    events
}