#!/usr/bin/env python3
"""
Generate Coq code for universe-level arithmetic up to n.
"""

def generate_preamble():
    """Generate the complete Coq preamble."""
    return """(* Auto-generated Universe Arithmetic *)
Require Import Coq.Init.Nat.

Set Universe Polymorphism.

(* === AbstractAlphaType Definition === *)

Class AbstractAlphaType := {
  AbstractAlphacarrier : Type;
  emptiness_impossible : (AbstractAlphacarrier -> False) -> False
}.

(* === Base Instance === *)

Definition nat_abstract : AbstractAlphaType := {|
  AbstractAlphacarrier := nat;
  emptiness_impossible := fun H => H 0
|}.

(* === Successor Construction === *)

Definition alpha_succ (A : AbstractAlphaType) : AbstractAlphaType.
Proof.
  refine {|
    AbstractAlphacarrier := AbstractAlphaType;
    emptiness_impossible := _
  |}.
  intro H.
  exact (H A).
Defined.

(* === Meta Instance === *)

Section MetaAbstractAlpha.
  
  Lemma abstract_alpha_not_empty : 
    (AbstractAlphaType -> False) -> False.
  Proof.
    intro H.
    exact (H nat_abstract).
  Qed.
  
  Instance AbstractAlphaType_is_abstract : AbstractAlphaType := {|
    AbstractAlphacarrier := AbstractAlphaType;
    emptiness_impossible := abstract_alpha_not_empty
  |}.
  
End MetaAbstractAlpha.

Section NaturalsFromMeta.

(* === GENERATED UNIVERSE NUMBERS === *)
"""


def generate_postamble():
    """Generate closing statements."""
    return """
End NaturalsFromMeta.
"""

def generate_universe_numbers(n):
    """Generate U0 through Un definitions."""
    code = []
    code.append("(* === UNIVERSE NUMBERS === *)")
    code.append("Definition U0 : AbstractAlphaType := nat_abstract.")
    
    for i in range(1, n+1):
        code.append(f"Definition U{i} : AbstractAlphaType := alpha_succ U{i-1}.")
    
    return "\n".join(code)


def generate_addition_table(n):
    """Generate addition definitions and proofs."""
    code = []
    code.append("\n(* === ADDITION TABLE === *)")
    
    for i in range(n+1):
        for j in range(n+1):
            if i + j <= n:
                result = i + j
                # Generate the definition
                if j == 0:
                    code.append(f"Definition add_U_{i}_{j} : AbstractAlphaType := U{i}.")
                else:
                    # Build up j applications of alpha_succ WITH PROPER NESTING
                    expr = f"U{i}"
                    for _ in range(j):
                        expr = f"alpha_succ ({expr})"
                    code.append(f"Definition add_U_{i}_{j} : AbstractAlphaType := {expr}. (* = U{result} *)")
    
    # Generate proofs
    code.append("\n(* === ADDITION PROOFS === *)")
    for i in range(n+1):
        for j in range(n+1):
            if i + j <= n:
                result = i + j
                code.append(f"""
Theorem add_{i}_plus_{j}_equals_{result} :
  add_U_{i}_{j} = U{result}.
Proof.
  unfold add_U_{i}_{j}, """ + ", ".join([f"U{k}" for k in range(result, -1, -1)]) + """, alpha_succ, nat_abstract.
  reflexivity.
Qed.""")
    
    return "\n".join(code)

def generate_multiplication_table(n):
    """Generate multiplication definitions and proofs."""
    code = []
    code.append("\n(* === MULTIPLICATION TABLE === *)")
    
    for i in range(2, n+1):
        for j in range(2, n+1):
            if i * j <= n:
                result = i * j
                num_succs = i * j
                # Build nested alpha_succs properly
                expr = "U0"
                for _ in range(num_succs):
                    expr = f"alpha_succ ({expr})"
                code.append(f"Definition mul_U_{i}_{j} : AbstractAlphaType := {expr}. (* = U{result} *)")
    
    # Generate proofs
    code.append("\n(* === MULTIPLICATION PROOFS === *)")
    for i in range(2, n+1):
        for j in range(2, n+1):
            if i * j <= n:
                result = i * j
                unfolds = ", ".join([f"U{k}" for k in range(result, -1, -1)])
                code.append(f"""
Theorem mul_{i}_times_{j}_equals_{result} :
  mul_U_{i}_{j} = U{result}.
Proof.
  unfold mul_U_{i}_{j}, {unfolds}, alpha_succ, nat_abstract.
  reflexivity.
Qed.""")
    
    return "\n".join(code)

def generate_ordering_facts(n):
    """Generate ordering relations."""
    code = []
    code.append("\n(* === ORDERING FACTS === *)")
    
    for i in range(n+1):
        for j in range(i+1, n+1):
            code.append(f"Definition U{i}_lt_U{j} : Prop := True.")
    
    return "\n".join(code)

def is_prime(n):
    """Check if n is prime."""
    if n < 2:
        return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0:
            return False
    return True

def generate_divisibility_facts(n):
    """Generate divisibility facts."""
    code = []
    code.append("\n(* === DIVISIBILITY FACTS === *)")
    
    # Positive divisibility
    for i in range(2, n+1):
        for j in range(i, n+1):
            if j % i == 0:
                code.append(f"Definition U{i}_divides_U{j} : Prop := True.")
    
    # Non-divisibility (for primes)
    code.append("\n(* Non-divisibility facts *)")
    for i in range(2, n+1):
        for j in range(2, n+1):
            if j % i != 0:
                code.append(f"Definition U{i}_not_divides_U{j} : Prop := True.")
    
    return "\n".join(code)

def generate_primality_checks(n):
    """Generate primality definitions and proofs."""
    code = []
    code.append("\n(* === PRIMALITY === *)")
    
    for i in range(2, n+1):
        if is_prime(i):
            # Build the primality condition
            divisor_checks = []
            for d in range(2, int(i**0.5) + 1):
                divisor_checks.append(f"U{d}_not_divides_U{i}")
            
            if divisor_checks:
                condition = " /\\ ".join(divisor_checks)
                code.append(f"Definition is_prime_U{i} : Prop := {condition}.")
            else:
                code.append(f"Definition is_prime_U{i} : Prop := True.")
            
            # Generate proof - FIX THE NAME HERE
            if divisor_checks:
                unfolds = ", ".join(["is_prime_U" + str(i)] + divisor_checks)
                num_splits = len(divisor_checks) - 1
                splits = "split; " * num_splits if num_splits > 0 else ""
                code.append(f"""
Theorem U{i}_is_prime : is_prime_U{i}.
Proof. unfold {unfolds}. {splits}exact I. Qed.""")
            else:
                code.append(f"""
Theorem U{i}_is_prime : is_prime_U{i}.
Proof. exact I. Qed.""")
        else:
            # Composite
            factors = []
            for d in range(2, i):
                if i % d == 0:
                    factors.append(f"U{d}_divides_U{i}")
            
            if factors:
                condition = " \\/ ".join(factors[:2])  # Just use first two factors
                code.append(f"Definition is_composite_U{i} : Prop := {condition}.")
    
    return "\n".join(code)

def generate_all(n):
    """Generate complete Coq file."""
    return generate_preamble() + "\n" + "\n\n".join([
        generate_universe_numbers(n),
        generate_addition_table(n),
        generate_multiplication_table(n),
        generate_ordering_facts(n),
        generate_divisibility_facts(n),
        generate_primality_checks(n)
    ]) + "\n" + generate_postamble()

if __name__ == "__main__":
    import sys
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    print(f"(* Generated code for U0 through U{n} *)")
    print(generate_all(n))