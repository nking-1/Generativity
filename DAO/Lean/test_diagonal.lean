import DAO.Logic.Diagonal

/-! Test the revolutionary diagonal argument results -/

variable {Α : AlphaType} {Ω : OmegaType}

-- Key diagonal theorems that show unrepresentability creates meaning
#check @alpha_diagonal_differs Α
#check @omega_diagonal_not_representable Α Ω  
#check @incompleteness_from_diagonal Α Ω
#check @diagonal_creates_boundaries Α Ω

-- Demonstrate the core insight: some predicates cannot be enumerated
example (enum : AlphaEnum Α) : ∀ n, enum n ≠ some (alpha_diagonal_pred enum n) :=
  diagonal_not_enumerated enum

-- Demonstrate unrepresentability: Omega contains predicates Alpha cannot track
example (enum : AlphaEnum Α) (complete : enum_complete enum) (embed : Α.Α → Ω.Ω) :
  ¬@representable Α Ω (omega_diagonal enum embed) :=
  omega_diagonal_not_representable enum complete embed

-- Demonstrate Gödel-style incompleteness from diagonal argument  
example (enum : AlphaEnum Α) (complete : enum_complete enum) (embed : Α.Α → Ω.Ω) :
  let G := godel_statement enum embed
  G ∧ ¬∃ (A : Α.Α → Prop), (∃ a, A a) ∧ (∀ a, omega_diagonal enum embed (embed a) → A a) :=
  incompleteness_from_diagonal enum complete embed