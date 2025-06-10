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
