from unravel_v3 import *

# Test 1: What are these expressions actually evaluating to?
print("=== INVESTIGATING EQUIVALENCE ===")
expr1 = Ex.mul(Ex.num(3), Ex.num(5))
result1, universe1 = run_thermo(expr1)
print(f"3 * 5 = {result1.value if hasattr(result1, 'value') else result1}")
print(f"Entropy: {universe1.total_entropy}")

expr2 = Ex.add(Ex.num(3), Ex.num(5))
result2, universe2 = run_thermo(expr2)
print(f"3 + 5 = {result2.value if hasattr(result2, 'value') else result2}")
print(f"Entropy: {universe2.total_entropy}")

print(f"Are they equal? {result1.value == result2.value if hasattr(result1, 'value') and hasattr(result2, 'value') else 'N/A'}")
print()

# Test 2: Let's test Noether with some edge cases
print("=== MORE NOETHER TESTS ===")
# Same expression
same = MathematicalVerifier.test_noether_theorem(Ex.num(42), Ex.num(42))
print(f"42 ≡ 42: {same}")

# Different numbers
diff = MathematicalVerifier.test_noether_theorem(Ex.num(42), Ex.num(7))
print(f"42 ≡ 7: {diff}")

# Void equivalence
void1 = Ex.div(Ex.num(1), Ex.num(0))
void2 = Ex.div(Ex.num(2), Ex.num(0))
void_equiv = MathematicalVerifier.test_noether_theorem(void1, void2)
print(f"void(1/0) ≡ void(2/0): {void_equiv}")
print()

# Test 3: Modulo operation
print("=== MODULO OPERATION ===")
mod_normal = Ex.mod(Ex.num(17), Ex.num(5))
result3, universe3 = run_thermo(mod_normal)
print(f"17 % 5 = {result3.value if hasattr(result3, 'value') else result3}")

mod_by_zero = Ex.mod(Ex.num(17), Ex.num(0))
result4, universe4 = run_thermo(mod_by_zero)
print(f"17 % 0 = {result4}")
print(f"Type: {type(result4).__name__}")