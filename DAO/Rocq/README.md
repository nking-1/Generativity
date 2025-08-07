# DAO Framework

DAO (Duality of Alpha and Omega) is a framework that constructs logic and mathematics from first principles based on an interplay of two types: OmegaType, a trivial, fully complete type with a proof for anything, and AlphaType, a consistent but incomplete type that acknowledges impossibility. The framework is named DAO as an homage to Daoism, which strongly aligns with the fundamental principles uncovered by the Omega, Alpha, and Nomega types.

DAO is designed to be a free, open source library for mathematics. Feel free to use it in your work. Please cite the author (Nicholas King) and the record on Zenodo if you use it. DAO is currently in a pre-release stage, so APIs might change significantly in future versions.

## Recommended Reading Order
Try reading the proofs in `DAO/Rocq/src/Core` in this order:

1. OmegaType.v and OmegaProperties.v - See how triviality results in immediate contradiction.
2. NomegaType.v and NomegaProperties.v - See how emptiness results in vacuous non-existence.
3. AlphaType.v and AlphaProperties.v - Observe the beginning of structure emergent from one impossibility.

From there, you can choose to read the proofs as you like:

- `DAO/Rocq/src/Logic` - Shows how ternary logic, diagonal arguments, and classic unrepresentability results emerge.
- `DAO/Rocq/src/Logic/Paradox` - Shows how Alpha absorbs all paradox into its impossible predicate, while Omega uses paradox constructively.
- `DAO/Rocq/src/Theory/Impossibility` - Implements a new theory, impossibility theory, from the unique impossible predicate of AlphaType.
- `DAO/Rocq/src/Classical` - Defines ClassicalAlphaType, which explicitly uses the law of excluded middle (classical logic), and then rebuilds classical mathematics using it.
- `DAO/Rocq/src/Metaphysics/Process.v` - Shows why process / impermanence (anicca) is a logical necessity to avoid paradox.
- `DAO/Rocq/src/Core/GenerativeType.v` and `DAO/Rocq/src/Core/GenerativeProperties.v` - Builds a special type that can approximate Omega through temporal separation, while avoiding collapse into complete paradox.
- `DAO/Rocq/src/Metaphysics/Metaphysics.v` - Explores building metaphysical, philosophical, and theological proofs using the GenerativeType. Please note, this is intended to be a demonstration of how such proofs can be written, not an imposition of fact about a particular religious stance.

## Building the Library
This project requires Rocq 9.0 or newer. To build the library and verify the proofs, run `make` in the `Rocq/` directory. Please file an issue on GitHub if it does not build for you.

## Future work
- Expand impossibility theory
- Expand computational metaphysics theory
- Port to Lean