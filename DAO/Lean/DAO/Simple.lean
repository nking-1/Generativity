import DAO.Core

/-!
# Simple DAO Examples

Just the basic theorems to get the framework working.
-/

/-- Omega makes everything true, including contradictions -/
theorem omega_makes_everything_true (Ω : OmegaType) : 
  ∃ x : Ω.Ω, True ∧ ¬True := 
  omega_paradox Ω (fun _ => True)

/-- omega_veil is the unique impossible predicate in Alpha -/
theorem omega_veil_unique_alpha (Α : AlphaType) :
  ∃ P : Α.Α → Prop, (∀ x, ¬P x) ∧ 
  (∀ Q : Α.Α → Prop, (∀ x, ¬Q x) → Q = P) := by
  exists ω_veil Α
  exact ⟨Α.unique_impossible, Α.everything_else_possible⟩

/-- The fundamental duality: Omega complete, Alpha incomplete -/
theorem omega_alpha_duality (Ω : OmegaType) (Α : AlphaType) :
  (∀ P : Ω.Ω → Prop, ∃ x, P x) ∧ 
  (∃ P : Α.Α → Prop, ∀ x, ¬P x) := by
  constructor
  · exact Ω.completeness
  · exists ω_veil Α
    exact Α.unique_impossible