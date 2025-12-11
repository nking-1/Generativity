# **DAO Framework**

**DAO (Duality of Alpha and Omega)** is a foundational framework that reconstructs logic and mathematics from first principles using *impossibility* as its primitive concept. It is based on the interaction of two types:

* **OmegaType** — an over-complete type where *everything is provable*, collapsing into paradox.
* **AlphaType** — a consistent but incomplete type that contains *exactly one* impossible predicate (the omega-veil), enabling structured mathematics.
* **VoidType** — the dual extreme: absolute emptiness, collapsing into vacuity.

From these extremes, DAO develops a logic based not on truth but on **controlled impossibility**, recovering classical and constructive mathematics as emergent phenomena. The name *DAO* is an homage to Daoist metaphysics, which unexpectedly mirrors the mathematical structure uncovered in Omega, Alpha, and Void.

DAO is fully open source. Please cite the author (Nicholas King) and the Zenodo record if you use it. The framework is currently in pre-release; APIs may change significantly as the theory evolves.

---

## **Recommended Reading Order**

A good place to begin is in `DAO/Rocq/src/Core`:

1. **OmegaType.v, OmegaProperties.v**

   * See how complete overdetermination leads to immediate contradiction.

2. **VoidType.v, VoidProperties.v**

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
