import DAO.Temporal

/-! Test file to demonstrate key GenerativeType theorems -/

variable {Α : AlphaType} [G : GenerativeType Α]

#check @gen_simultaneous_negation_t0 Α G
#check @free_will_implies_suffering Α G  
#check @gen_time_allows_paradox Α G
#check @gen_contains_liars_paradox_t0 Α G
#check @gen_never_complete Α G

-- Demonstrate the key insight: t=0 contains ALL predicates and their negations
example : ∀ P : (Α.Α → Prop) → Prop,
  G.contains 0 (G.self_ref_pred_embed P) ∧
  G.contains 0 (G.self_ref_pred_embed (fun pred => ¬P pred)) :=
  gen_simultaneous_negation_t0