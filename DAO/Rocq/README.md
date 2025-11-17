# DAO Framework

DAO (Duality of Alpha and Omega) is a framework that constructs logic and mathematics from first principles based on an interplay of two types: OmegaType, a trivial, fully complete type with a proof for anything, and AlphaType, a consistent but incomplete type that acknowledges impossibility. DAO constructs logic from impossibility: Omega represents total overdetermination, Alpha represents consistent limitation, and their interplay generates mathematics. The framework is named DAO as an homage to the intuitions of Daoism, which strongly aligns with the fundamental principles uncovered by the Omega, Alpha, and Nomega types.

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
- `DAO/Rocq/src/Metaphysics/Process.v` - Builds a generative incompleteness theorem that conceptually echoes process philosophy / impermanence (anicca)

# **DAO Framework**

**DAO (Duality of Alpha and Omega)** is a foundational framework that reconstructs logic and mathematics from first principles using *impossibility* as its primitive concept. It is based on the interaction of two types:

* **OmegaType** — an over-complete type where *everything is provable*, collapsing into paradox.
* **AlphaType** — a consistent but incomplete type that contains *exactly one* impossible predicate (the omega-veil), enabling structured mathematics.
* **NomegaType** — the dual extreme: absolute emptiness, collapsing into vacuity.

From these extremes, DAO develops a logic based not on truth but on **controlled impossibility**, recovering classical and constructive mathematics as emergent phenomena. The name *DAO* is an homage to Daoist metaphysics, which unexpectedly mirrors the mathematical structure uncovered in Omega, Alpha, and Nomega.

DAO is fully open source. Please cite the author (Nicholas King) and the Zenodo record if you use it. The framework is currently in pre-release; APIs may change significantly as the theory evolves.

---

## **Recommended Reading Order**

A good place to begin is in `DAO/Rocq/src/Core`:

1. **OmegaType.v, OmegaProperties.v**

   * See how complete overdetermination leads to immediate contradiction.

2. **NomegaType.v, NomegaProperties.v**

   * See how emptiness leads to triviality through vacuity.

3. **AlphaType.v, AlphaProperties.v**

   * See how *one* impossible predicate is sufficient to generate consistent structure.

After this foundation:

* `DAO/Rocq/src/Logic`
  Diagonal arguments, paradox analysis, ternary logic, unrepresentability.

* `DAO/Rocq/src/Logic/Paradox`
  How Alpha absorbs paradox into a controlled structure while Omega uses it constructively.

* `DAO/Rocq/src/Theory/Impossibility`
  A new theory—*impossibility theory*—built on the unique impossible predicate of AlphaType.

* `DAO/Rocq/src/Classical`
  A ClassicalAlphaType implementing classical logic (LEM) and rebuilding classical mathematics constructively.

* `DAO/Rocq/src/Metaphysics/Process.v`
  A generative incompleteness theorem with connections to process philosophy.

* `DAO/Rocq/src/Core/GenerativeType.v` and `DAO/Rocq/src/Core/GenerativeProperties.v`
  A special type that can approximate Omega through temporal separation, while avoiding collapse into complete paradox.

* `DAO/Rocq/src/Metaphysics/Metaphysics.v`
  Explores building metaphysical, philosophical, and theological proofs using the GenerativeType. Please note, this is intended to be a demonstration of how such proofs can be written, not an imposition of fact about a particular religious stance.

---

## **Building the Library**

Requires **Rocq 9.0 or newer**.
To build:

```bash
cd Rocq/
make
```

Please open an issue if you encounter build problems.

---

## **Future Work**

* Expand impossibility theory
* Extend computational metaphysics
* Unify classical set theory and impossibility geometry
* Port the framework to Lean
