# Classical Folder Refactoring Plan

## Overview
The `alpha_set_classical.v` file in Legacy contains 1865 lines implementing ClassicalAlphaType and various mathematical theories. This should be split into modular files in the `src/Classical/` folder.

## Proposed File Structure

### 1. **ClassicalAlphaType.v** (Lines 1-147)
- Core type class definition
- Basic properties of omega_veil
- Fundamental theorems (excluded middle, double negation)
- Spatial characterization

### 2. **ClassicalPredicates.v** (Lines 148-337)
- Predicate polarity trichotomy
- Helper lemmas for predicate logic
- The necessary predicate
- Predicate trichotomy classification

### 3. **ClassicalBooleanAlgebra.v** (Lines 338-540)
- Boolean operations on predicates
- Boolean algebra laws (commutativity, associativity, distributivity)
- Identity and complement laws
- De Morgan's laws
- Boolean algebra classification theorem

### 4. **ClassicalParadoxFirewalls.v** (Lines 541-653)
- Russell's paradox firewall
- Curry's paradox firewall
- Liar paradox firewall
- Self-denying existence firewall
- Predicate grounding theorem

### 5. **ClassicalArithmetic.v** (Lines 654-898)
- Natural numbers encoding
- Zero, successor, addition, multiplication
- Basic arithmetic properties
- Prime number definitions

### 6. **ClassicalPrimesTheorem.v** (Lines 899-1072)
- Euclid's infinitude of primes
- Supporting lemmas for the proof
- Divisibility properties
- Product constructions

### 7. **ClassicalZFC.v** (Lines 1073-1865)
- ZFC axioms in ClassicalAlphaType
- Sets as predicates
- Membership relations
- All ZFC axioms:
  - Extensionality
  - Empty set
  - Pairing
  - Union
  - Separation
  - Power set
  - Infinity
  - Replacement
  - Foundation/Regularity
  - Choice

## Module Dependencies

```
ClassicalAlphaType.v
    ↓
ClassicalPredicates.v
    ↓
ClassicalBooleanAlgebra.v
    ↓
ClassicalParadoxFirewalls.v

ClassicalArithmetic.v
    ↓
ClassicalPrimesTheorem.v

ClassicalZFC.v (depends on ClassicalAlphaType.v)
```

## Refactoring Steps

1. **Create ClassicalAlphaType.v**: Extract core type class and basic properties
2. **Create ClassicalPredicates.v**: Extract predicate-specific theorems
3. **Create ClassicalBooleanAlgebra.v**: Extract boolean algebra implementation
4. **Create ClassicalParadoxFirewalls.v**: Extract paradox-related theorems
5. **Create ClassicalArithmetic.v**: Extract natural number construction
6. **Create ClassicalPrimesTheorem.v**: Extract Euclid's proof
7. **Create ClassicalZFC.v**: Extract ZFC implementation

## Import Structure

Each file should import:
- `Require Import Setoid.` (where needed)
- Previous modules in the dependency chain
- Core DAO modules as needed (likely none for classical logic)

## Benefits of This Structure

1. **Modularity**: Each mathematical concept in its own file
2. **Reusability**: Other theories can import just what they need
3. **Clarity**: Clear separation between foundational logic and specific theories
4. **Maintainability**: Easier to modify individual components
5. **Documentation**: Each file can have focused documentation

## Notes

- The existing `ClassicalAlphaType.v` and `ClassicalAlphaProperties.v` in Core should remain there
- These new files implement specific classical mathematical theories using the core type
- Consider adding a `Classical.v` file that re-exports all classical modules for convenience