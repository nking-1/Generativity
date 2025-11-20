from unravel_v3 import *

# Test 1: Saturating subtraction (never goes negative)
print("=== SATURATING SUBTRACTION ===")
normal_sub = Ex.sub(Ex.num(10), Ex.num(3))
result1, universe1 = run_thermo(normal_sub)
print(f"10 - 3 = {result1.value if hasattr(result1, 'value') else result1}")

underflow = Ex.sub(Ex.num(3), Ex.num(10))
result2, universe2 = run_thermo(underflow)
print(f"3 - 10 = {result2.value if hasattr(result2, 'value') else result2}")
print(f"Type: {type(result2).__name__}")
print(f"Entropy: {universe2.total_entropy}")
print()

# Test 2: Mathematical verification - Noether's theorem (equivalence)
print("=== NOETHER'S THEOREM (EQUIVALENCE) ===")
expr_a = Ex.add(Ex.num(5), Ex.num(10))
expr_b = Ex.add(Ex.num(10), Ex.num(5))
equivalent = MathematicalVerifier.test_noether_theorem(expr_a, expr_b)
print(f"5 + 10 ≡ 10 + 5: {equivalent}")

# Try with something that shouldn't be equivalent
expr_c = Ex.mul(Ex.num(3), Ex.num(5))
expr_d = Ex.add(Ex.num(3), Ex.num(5))
not_equiv = MathematicalVerifier.test_noether_theorem(expr_c, expr_d)
print(f"3 * 5 ≡ 3 + 5: {not_equiv}")
print()

# Test 3: Conservation law (entropy preservation through recovery)
print("=== CONSERVATION LAW ===")
void_expr = Ex.div(Ex.num(10), Ex.num(0))
fallback = Ex.num(99)
conserved = MathematicalVerifier.test_conservation_law(void_expr, fallback)
print(f"Entropy preserved through recovery: {conserved}")
print()

# Test 4: Base veil principle
print("=== BASE VEIL PRINCIPLE ===")
void_expr2 = Ex.div(Ex.num(42), Ex.num(0))
has_entropy = MathematicalVerifier.test_base_veil_principle(void_expr2)
print(f"Void has entropy >= 1: {has_entropy}")