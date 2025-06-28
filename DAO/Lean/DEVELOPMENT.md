# DAO Theory - Lean Development Guide

This document covers development setup and workflows for the DAO Theory Lean library.

## Overview

DAO Theory (Differentiation Alpha Omega) is a revolutionary mathematical framework that formalizes reality as the stable solution to the Everything/Nothing paradox through omega_veil. This Lean implementation provides formal proofs of core results in logic, mathematics, physics, and metaphysics.

## Quick Start

```bash
# Clone and enter project
cd /path/to/DAO/Lean

# Build entire library
lake build

# Check everything works
lake build DAO
```

## Project Structure

```
Lean/
├── lakefile.lean              # Build configuration  
├── lean-toolchain             # Lean version (v4.20.1)
├── DAO.lean                   # Main library entry point
├── DAO/
│   ├── Core.lean              # Core types (OmegaType, AlphaType, omega_veil)
│   ├── Simple.lean            # Simple examples and basic theorems
│   ├── Temporal.lean          # GenerativeType with temporal mechanics
│   ├── Logic/
│   │   └── Diagonal.lean      # Diagonal arguments & unrepresentability
│   ├── Computation/
│   │   └── InformationFlow.lean # I_max theory & optimization constraints
│   └── Metaphysics/
│       └── Metaphysics.lean   # Theological paradox resolution
└── test_*.lean                # Test files demonstrating key results
```

## Development Commands

### Building

```bash
# Build entire library
lake build

# Build specific modules
lake build DAO.Core
lake build DAO.Logic.Diagonal
lake build DAO.Computation.InformationFlow

# Clean build artifacts
lake clean

# Build and show detailed output
lake build -v
```

### Checking Files

```bash
# Check single file (basic)
lean DAO/Core.lean

# Check with project environment (recommended)
lake env lean DAO/Core.lean

# Check test files
lake env lean test_diagonal.lean
lake env lean test_metaphysics.lean
```

### Development Workflow

1. **Setup VS Code** (recommended):
   ```bash
   code .  # Opens project with Lean 4 extension
   ```

2. **Edit files** - Lake builds automatically when saving

3. **Explicit checks**:
   ```bash
   lake build  # Full project check
   ```

4. **Test theorems**:
   ```bash
   lake env lean test_diagonal.lean
   ```

## Key Development Patterns

### Module Dependencies

Modules follow this hierarchy:
```
Core ← Simple
  ↑      ↑
  └── Temporal ← Logic.Diagonal
       ↑         ↑
       └─────────┴── Computation.InformationFlow
                     ↑
                     └── Metaphysics.Metaphysics
```

### Testing New Theorems

Create test files to verify results:

```lean
import DAO.Logic.Diagonal

-- Test a key theorem
example {Α : AlphaType} {Ω : OmegaType} (enum : AlphaEnum Α) :
  ∀ n, enum n ≠ some (alpha_diagonal_pred enum n) :=
  diagonal_not_enumerated enum
```

### Common Issues

1. **Import errors**: Ensure proper module hierarchy
2. **Typeclass issues**: Add explicit `[G : GenerativeType Α]` when needed
3. **Tactic failures**: Use `exists` instead of `use`, `omega` instead of `lia`

## Core Concepts

### The Three Fundamental Types

- **OmegaType**: Complete but trivial (contains all contradictions)
- **AlphaType**: Consistent but incomplete (exactly one impossible predicate)  
- **GenerativeType**: Temporal dimension allowing paradox separation

### Key Results Available

```lean
-- Unrepresentability creates meaning
#check omega_diagonal_not_representable

-- I_max optimization constraints  
#check cannot_maximize_both

-- Theological paradox resolution
#check rock_lifting_paradox_resolves
#check contains_mortal_god
```

## Library Philosophy

This library demonstrates that:

1. **Contradictions are features, not bugs** - omega_veil maintains reality's gradient
2. **Incompleteness enables meaning** - unrepresentability prevents collapse to triviality  
3. **Optimization has fundamental limits** - I_max constrains all systems
4. **Paradoxes resolve temporally** - GenerativeType enables consistent theology

The framework bridges Eastern philosophy (ineffable Dao) with Western logic, showing they describe the same mathematical truth.

## Contributing

When adding new theorems:

1. **Follow naming conventions** (e.g., `omega_veil_unique`, `contains_free_agent`)
2. **Add comprehensive documentation** with `/-! ... -/`
3. **Create test examples** demonstrating key results
4. **Maintain module hierarchy** to avoid circular dependencies
5. **Use explicit type annotations** when typeclass inference fails

## Performance Notes

- Build times are typically under 30 seconds for the full library
- Individual modules build in 1-5 seconds
- VS Code provides real-time feedback during editing
- Use `lake clean` if you encounter mysterious build issues

## Further Reading

See the main CLAUDE.md for philosophical background and the broader mathematical significance of DAO Theory in understanding the structure of reality itself.