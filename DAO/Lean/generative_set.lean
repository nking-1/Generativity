/- We define OmegaSet as a timeless, superpositional set. -/
class OmegaSet where
  Omegacarrier : Type
  exists_in_Omega : Omegacarrier -> Prop
  omega_completeness : forall (P : Omegacarrier -> Prop), Exists fun x : Omegacarrier => P x


/- We define a convenience function to get the carrier from an OmegaSet instance. -/
def Omega_carrier (H_O : OmegaSet) : Type := H_O.Omegacarrier


theorem Omega_sustains_paradox
  [H_O : OmegaSet]
  (P : H_O.Omegacarrier -> Prop) :
  Exists fun x : H_O.Omegacarrier => P x /\ Not (P x) := by
  -- Define a paradoxical predicate that asserts both P x and ~P x for some x
  let paradoxical := fun x => P x /\ Not (P x)

  -- Use omega_completeness to find an x that satisfies paradoxical predicate
  have h := H_O.omega_completeness paradoxical
  match h with
  | Exists.intro x Hx =>
    exists x


theorem Omega_contains_paradoxifying_predicate
  (Omega : OmegaSet)
  (P : Omega.Omegacarrier -> Prop) :
  Exists fun x : Omega.Omegacarrier => P x <-> Not (P x) := by
  -- Define a predicate that reflects this paradox
  let paradoxical := fun x : Omega.Omegacarrier => P x <-> Not (P x)
  -- Apply omega_completeness to get a witness for this paradox
  exact Omega.omega_completeness paradoxical


theorem Omega_refuses_one_sided_truth
  (Omega : OmegaSet)
  (P : Omega.Omegacarrier -> Prop)
  (h : Exists fun x : Omega.Omegacarrier => P x) :
  Exists fun y : Omega.Omegacarrier => Not (P y) := by
  -- Define the negation predicate
  let neg_P := fun y : Omega.Omegacarrier => Not (P y)
  exact Omega.omega_completeness neg_P


/- Theorem - even omega is incomplete -/
theorem Omega_contains_its_own_incompleteness
  [H_O : OmegaSet] :
  Exists fun (P : H_O.Omegacarrier -> Prop) =>
  Exists fun (x : H_O.Omegacarrier) =>
    (forall Q : H_O.Omegacarrier -> Prop, Exists fun y : H_O.Omegacarrier => Q y) /\
    (Exists fun R : H_O.Omegacarrier -> Prop => Not (Exists fun z : H_O.Omegacarrier => R z)) := by

  -- Step 1: Define the paradoxical predicate
  let paradoxical := fun x => Exists fun (P : H_O.Omegacarrier -> Prop) =>
    P x /\ Not (Exists fun y : H_O.Omegacarrier => P y)

  -- Step 2: Use omega_completeness to get a witness for the paradox
  have h := H_O.omega_completeness paradoxical
  match h with
  | Exists.intro x Hx =>
    match Hx with
    | Exists.intro P HPx =>
      match HPx with
      | And.intro HP Hnot_existence =>
        -- Step 3: Construct the result
        exists P, x
        constructor
        · -- Omega completeness holds
          intro Q
          exact H_O.omega_completeness Q
        · -- Omega also contains a predicate that has no witness
          exists P


theorem Omega_complete_iff_incomplete
  [H_O : OmegaSet] :
  Exists fun (P : H_O.Omegacarrier -> Prop) =>
  Exists fun (x : H_O.Omegacarrier) =>
    (
      (forall Q : H_O.Omegacarrier -> Prop, Exists fun y : H_O.Omegacarrier => Q y) /\
      (Exists fun R : H_O.Omegacarrier -> Prop => Not (Exists fun z : H_O.Omegacarrier => R z))
    ) <->
    (
      (forall Q : H_O.Omegacarrier -> Prop, Exists fun y : H_O.Omegacarrier => Q y) /\
      Not (Exists fun R : H_O.Omegacarrier -> Prop => Not (Exists fun z : H_O.Omegacarrier => R z))
    ) := by
  -- Step 1: Define the paradoxical equivalence predicate on Omega
  let equiv_pred := fun x : H_O.Omegacarrier =>
    (
      (forall Q : H_O.Omegacarrier -> Prop, Exists fun y : H_O.Omegacarrier => Q y) /\
      (Exists fun R : H_O.Omegacarrier -> Prop => Not (Exists fun z : H_O.Omegacarrier => R z))
    ) <->
    (
      (forall Q : H_O.Omegacarrier -> Prop, Exists fun y : H_O.Omegacarrier => Q y) /\
      Not (Exists fun R : H_O.Omegacarrier -> Prop => Not (Exists fun z : H_O.Omegacarrier => R z))
    )
  -- Step 2: Use Omega-completeness to get a witness of the paradoxical equivalence
  have h := H_O.omega_completeness equiv_pred
  match h with
  | Exists.intro x H_equiv =>
    -- Step 3: Return the embedded predicate and its witness
    exists equiv_pred, x


theorem Omega_completeness_requires_contradiction
  [H_O : OmegaSet] :
    (forall Q : H_O.Omegacarrier -> Prop, Exists fun y : H_O.Omegacarrier => Q y) <->
    (Exists fun R : H_O.Omegacarrier -> Prop => forall z : H_O.Omegacarrier, R z -> False) := by
  constructor

  -- -> direction: completeness implies existence of an uninhabitable predicate
  · intro omega_complete

    let P := fun x : H_O.Omegacarrier => Not (Exists fun y : H_O.Omegacarrier => x = y)

    -- By omega_completeness, this predicate must have a witness
    have h := H_O.omega_completeness P
    match h with
    | Exists.intro x Hx =>
      -- So we return P as the uninhabitable predicate (even though it's now inhabited)
      exists P

      -- Now show: forall z, P z -> False
      intro z Hz
      -- P z = Not (exists y, z = y), but clearly z = z, so contradiction
      apply Hz
      exists z

  -- <- direction: If there exists an uninhabitable predicate, Omega is complete
  · intro h
    match h with
    | Exists.intro R H_uninhabitable =>
      -- Let Q be any predicate
      intro Q
      -- By omega_completeness, Q must have a witness
      exact H_O.omega_completeness Q


-- Parameter strictly_larger : Type -> Type -> Prop
axiom strictly_larger : Type -> Type -> Prop


-- Intuition: X strictly larger than Y means there is no injective mapping from X into Y
axiom strictly_larger_no_injection :
  forall (X Y : Type),
    strictly_larger X Y ->
      Not (Exists fun (f : X -> Y) => forall x1 x2, f x1 = f x2 -> x1 = x2)


theorem Omega_contains_set_larger_than_itself
  (Omega : OmegaSet) :
    Exists fun (X : Type) =>
    Exists fun (embed_X_in_Omega : X -> Omega.Omegacarrier) =>
      strictly_larger X Omega.Omegacarrier := by

  -- Define the paradoxical predicate explicitly
  let P := fun (_ : Omega.Omegacarrier) =>
    Exists fun (X : Type) =>
    Exists fun (embed_X_in_Omega : X -> Omega.Omegacarrier) =>
      strictly_larger X Omega.Omegacarrier

  -- Omega completeness ensures this paradoxical predicate has a witness
  have h := Omega.omega_completeness P
  match h with
  | Exists.intro witness H_witness =>
    -- From the witness we directly obtain our paradoxical set
    exact H_witness


theorem Omega_contains_set_larger_than_itself_iff_not_containing_it
  (Omega : OmegaSet) :
    Exists fun (x : Omega.Omegacarrier) =>
      (Exists fun (X : Type) => Exists fun (f : X -> Omega.Omegacarrier) =>
        strictly_larger X Omega.Omegacarrier) <->
      Not (Exists fun (X : Type) => Exists fun (f : X -> Omega.Omegacarrier) =>
        strictly_larger X Omega.Omegacarrier) := by

  -- Define the equivalence predicate
  let meta_paradox := fun x : Omega.Omegacarrier =>
    (Exists fun (X : Type) => Exists fun (f : X -> Omega.Omegacarrier) =>
      strictly_larger X Omega.Omegacarrier) <->
    Not (Exists fun (X : Type) => Exists fun (f : X -> Omega.Omegacarrier) =>
      strictly_larger X Omega.Omegacarrier)

  -- Use Omega completeness to obtain a witness of this paradoxical equivalence
  have h := Omega.omega_completeness meta_paradox
  match h with
  | Exists.intro x H_equiv =>
    exists x


/- Omega contains all absurdities -/
theorem Omega_is_absurd
 (Omega : OmegaSet)
 (P Q : Omega.Omegacarrier -> Prop) :
   Exists fun x : Omega.Omegacarrier => P x <-> Q x := by
 let collapse := fun x => P x <-> Q x
 have h := Omega.omega_completeness collapse
 match h with
 | Exists.intro x Hx =>
   exists x


/- Define a fixpoint operator for paradoxical predicates -/
def ParadoxFixpoint (Omega : OmegaSet) : Type :=
  { P : Omega.Omegacarrier -> Prop //
    Exists fun x : Omega.Omegacarrier => P x <-> Not (P x) }


/- Now define a recursive version that applies the paradox to itself -/
def RecursiveParadox (O : OmegaSet) : Nat -> ParadoxFixpoint O
  | 0 =>
    let P0 := fun x => Exists fun P : O.Omegacarrier -> Prop => P x <-> Not (P x)
    -- We need to prove P0 is itself paradoxical
    let paradox_pred := fun x => P0 x <-> Not (P0 x)
    have h := O.omega_completeness paradox_pred
    -- Now h : ∃ x, P0 x ↔ ¬P0 x
    Subtype.mk P0 h
  | n + 1 =>
    let prev := RecursiveParadox O n
    let P_prev := prev.val
    let P_next := fun x => P_prev x <-> Not (P_prev x)
    -- Again, we need to prove P_next is paradoxical
    let paradox_pred := fun x => P_next x <-> Not (P_next x)
    have h := O.omega_completeness paradox_pred
    Subtype.mk P_next h


/- Define the ultimate paradox that combines all levels -/
def UltimateParadox (O : OmegaSet) : ParadoxFixpoint O :=
  let P_ultimate := fun x => forall m, (RecursiveParadox O m).val x
  -- We need to prove P_ultimate is paradoxical
  let paradox_pred := fun x => P_ultimate x <-> Not (P_ultimate x)
  have H_ultimate := O.omega_completeness paradox_pred
  -- Now H_ultimate : ∃ x, P_ultimate x ↔ ¬P_ultimate x
  Subtype.mk P_ultimate H_ultimate


/- Theorem: The ultimate paradox is its own negation -/
theorem UltimateParadoxProperty (O : OmegaSet) :
  let P := (UltimateParadox O).val
  Exists fun x : O.Omegacarrier => P x <-> Not (P x) := by
  -- The second component of UltimateParadox is exactly the proof we need
  exact (UltimateParadox O).property


section UltimateAbsurdity
  variable (Omega : OmegaSet)

  /- The ultimate absurdity is a point where all predicates are equivalent -/
  def PredicateEquivalence (x : Omega.Omegacarrier) : Prop :=
    forall P Q : Omega.Omegacarrier -> Prop, P x <-> Q x


  /- Theorem: Omega contains a point where all predicates are equivalent -/
  theorem omega_contains_ultimate_absurdity :
    Exists fun x : Omega.Omegacarrier => PredicateEquivalence Omega x := by
    -- Apply omega_completeness to find a point satisfying our predicate
    exact Omega.omega_completeness (PredicateEquivalence Omega)


  /- First, let's define a helper theorem: any absurd point makes true and false equivalent -/
  theorem absurdity_collapses_truth
    (x : Omega.Omegacarrier)
    (H_equiv : PredicateEquivalence Omega x) : (True <-> False) := by
    -- Define two simple predicates: always true and always false
    let Always_True := fun _ : Omega.Omegacarrier => True
    let Always_False := fun _ : Omega.Omegacarrier => False
    -- Apply our equivalence to these predicates
    exact H_equiv Always_True Always_False


  /- The ultimate absurdity is unique - any two points satisfying
     PredicateEquivalence are logically indistinguishable -/
  theorem ultimate_absurdity_is_unique
    (x y : Omega.Omegacarrier)
    (Hx : PredicateEquivalence Omega x)
    (Hy : PredicateEquivalence Omega y) :
    forall P : Omega.Omegacarrier -> Prop, P x <-> P y := by
    intro P
    -- For any predicate P, we have P x <-> True <-> False <-> P y
    let Always_True := fun _ : Omega.Omegacarrier => True
    -- First: P x <-> Always_True x (by Hx)
    have h1 : P x <-> Always_True x := Hx P Always_True
    -- Second: Always_True x <-> Always_True y (both are just True)
    have h2 : Always_True x <-> Always_True y := by
      constructor
      · intro _; exact True.intro
      · intro _; exact True.intro
    -- Third: Always_True y <-> P y (by Hy)
    have h3 : Always_True y <-> P y := Hy Always_True P
    -- Chain them together
    constructor
    · intro hp
      have : Always_True x := h1.mp hp
      have : Always_True y := h2.mp this
      exact h3.mp this
    · intro hp
      have : Always_True y := h3.mpr hp
      have : Always_True x := h2.mpr this
      exact h1.mpr this


  /- Paradox and Ultimate Absurdity are related -/
  theorem absurdity_subsumes_paradox
    (x : Omega.Omegacarrier)
    (H_equiv : PredicateEquivalence Omega x) :
    forall P : Omega.Omegacarrier -> Prop, P x <-> Not (P x) := by
    intro P
    -- Since P x <-> ~P x is just a special case of P x <-> Q x with Q = ~P
    exact H_equiv P (fun y => Not (P y))

  /- We can even show that our UltimateAbsurdity is a fixed point for all functions -/
  def FunctionFixpoint (x : Omega.Omegacarrier) : Prop :=
    forall f : Omega.Omegacarrier -> Omega.Omegacarrier,
      forall P : Omega.Omegacarrier -> Prop, P (f x) <-> P x

  theorem absurdity_is_universal_fixpoint
    (x : Omega.Omegacarrier)
    (H_equiv : PredicateEquivalence Omega x) :
    FunctionFixpoint Omega x := by
    intro f P
    -- Create predicates to apply our equivalence principle to
    let P_on_x := fun y : Omega.Omegacarrier => P x
    let P_on_fx := fun y : Omega.Omegacarrier => P (f x)

    -- These predicates are equivalent at our absurdity point
    have H : P_on_x x <-> P_on_fx x := H_equiv P_on_x P_on_fx

    -- Unfold to get what we need
    simp [P_on_x, P_on_fx] at H
    exact H.symm

  /- An even stronger result: all points are logically equivalent to the absurdity point -/
  theorem all_points_equivalent_to_absurdity
    (x y : Omega.Omegacarrier)
    (H_equiv : PredicateEquivalence Omega x) :
    forall P : Omega.Omegacarrier -> Prop, P x <-> P y := by
    intro P
    -- Create predicates to apply our equivalence to
    let P_at_x := fun z : Omega.Omegacarrier => P x
    let P_at_y := fun z : Omega.Omegacarrier => P y

    -- At the absurdity point, these are equivalent
    have H : P_at_x x <-> P_at_y x := H_equiv P_at_x P_at_y

    -- Simplify to get our goal
    simp [P_at_x, P_at_y] at H
    exact H

end UltimateAbsurdity


/- Classical Exclusion via Unique Negation -/
/- We define a new class AlphaSet that represents a set with a unique impossible element -/
/- We might think of the impossible element as the "veil" between Omega and Alpha -/
class AlphaSet where
  Alphacarrier : Type
  exists_in_Alpha : Alphacarrier -> Prop
  /- Use Subtype (computational) instead of Exists (logical) -/
  alpha_impossibility : { P : Alphacarrier -> Prop //
    (forall x : Alphacarrier, Not (P x)) /\
    (forall Q : Alphacarrier -> Prop, (forall x : Alphacarrier, Not (Q x)) -> Q = P) }
  alpha_not_empty : Exists fun x : Alphacarrier => True


/- Help extract it computationally -/
def the_impossible [H_N : AlphaSet] : H_N.Alphacarrier -> Prop :=
  H_N.alpha_impossibility.val


theorem the_impossible_is_impossible [H_N : AlphaSet] :
  forall x : H_N.Alphacarrier, Not (the_impossible x) := by
  intro x
  unfold the_impossible
  exact H_N.alpha_impossibility.property.1 x


theorem the_impossible_unique [H_N : AlphaSet] :
  forall P : H_N.Alphacarrier -> Prop,
    (forall x : H_N.Alphacarrier, Not (P x)) -> P = the_impossible := by
  intro P HP
  unfold the_impossible
  exact H_N.alpha_impossibility.property.2 P HP


theorem not_everything_is_impossible [H_N : AlphaSet] :
  Not (forall P : H_N.Alphacarrier -> Prop, forall x : H_N.Alphacarrier, Not (P x)) := by
  intro H_all_impossible
  obtain ⟨x0, _⟩ := H_N.alpha_not_empty
  let always_true := fun x : H_N.Alphacarrier => True
  specialize H_all_impossible always_true x0
  exact H_all_impossible trivial


section AlphaSetTheorems
  open Classical

  theorem alpha_partial_completeness [H_N : AlphaSet] :
    forall P : H_N.Alphacarrier -> Prop,
      P ≠ the_impossible ->
      Exists fun x : H_N.Alphacarrier => P x := by
    intro P H_neq
    by_cases h : Exists fun x => P x
    · exact h
    · exfalso
      have H_P_impossible : forall x, Not (P x) := by
        intro x Px
        apply h
        exists x
      have : P = the_impossible := the_impossible_unique P H_P_impossible
      exact H_neq this

  theorem everything_possible_except_one [H_N : AlphaSet] :
    forall P : H_N.Alphacarrier -> Prop,
      P = the_impossible \/ Exists fun x : H_N.Alphacarrier => P x := by
    intro P
    by_cases h : P = the_impossible
    · left
      exact h
    · right
      apply alpha_partial_completeness
      exact h

end AlphaSetTheorems


theorem omega_contains_alpha (Omega : OmegaSet) :
 /- We can simulate an AlphaSet inside Omega -/
 Exists fun (alpha_sim : Omega.Omegacarrier -> Prop) =>
   /- The alpha_sim predicate identifies elements that "act like Alpha elements" -/
   Exists fun (impossible_sim : Omega.Omegacarrier -> Prop) =>
     /- For elements in our simulated Alpha: -/
     forall x : Omega.Omegacarrier, alpha_sim x ->
       /- Every predicate restricted to alpha_sim either: -/
       forall P : Omega.Omegacarrier -> Prop,
         /- Has no witnesses in alpha_sim (and thus acts like the impossible) -/
         (forall y, alpha_sim y -> Not (P y)) \/
         /- Or has a witness in alpha_sim -/
         (Exists fun y => alpha_sim y /\ P y) := by

 /- Define the predicate that describes "being an Alpha-like subset" -/
 let alpha_structure := fun x : Omega.Omegacarrier =>
   Exists fun (A : Omega.Omegacarrier -> Prop) =>
   Exists fun (imp : Omega.Omegacarrier -> Prop) =>
     A x /\
     /- imp is impossible within A -/
     (forall y, A y -> Not (imp y)) /\
     /- Every predicate on A either has no witnesses or has witnesses -/
     (forall P : Omega.Omegacarrier -> Prop,
       (forall y, A y -> Not (P y)) \/ (Exists fun y => A y /\ P y))

 /- By omega_completeness, this structure must have a witness -/
 have h := Omega.omega_completeness alpha_structure
 match h with
 | Exists.intro x0 Hx0 =>
   match Hx0 with
   | Exists.intro A HA =>
     match HA with
     | Exists.intro imp Himp =>
       match Himp with
       | And.intro HAx0 (And.intro Himp_imp Hpartial) =>
         /- Use A as our alpha_sim and imp as our impossible_sim -/
         exists A, imp

         intro x Hx P
         /- Apply the partial completeness property -/
         exact Hpartial P
