from unravel_v3 import *

# Test 1: Compare entropy of different operations
print("=== ENTROPY COMPARISON ===")
# These should all have entropy 0
exprs = [
    ("42", Ex.num(42)),
    ("7", Ex.num(7)),
    ("3 + 5", Ex.add(Ex.num(3), Ex.num(5))),
    ("10 * 10", Ex.mul(Ex.num(10), Ex.num(10)))
]

for name, expr in exprs:
    result, universe = run_thermo(expr)
    print(f"{name}: value={result.value if hasattr(result, 'value') else 'void'}, entropy={universe.total_entropy}")

print()

# Test 2: Compare void expressions with different sources
print("=== DIFFERENT VOID SOURCES ===")
void_exprs = [
    ("1/0", Ex.div(Ex.num(1), Ex.num(0))),
    ("100/0", Ex.div(Ex.num(100), Ex.num(0))),
    ("5%0", Ex.mod(Ex.num(5), Ex.num(0))),
    ("undefined_var", Ex.variable("xyz"))
]

for name, expr in void_exprs:
    result, universe = run_thermo(expr)
    print(f"{name}: entropy={universe.total_entropy}, void_count={universe.void_count}")
    if isinstance(result, VTVoid):
        print(f"  Source type: {type(result.info.source).__name__}")

# All have entropy 1, so they're "equivalent" under Noether?
print()

# Test 3: What about mixed entropy expressions?
print("=== MIXED ENTROPY TEST ===")
clean_expr = Ex.num(42)  # entropy 0
recovered_expr = Ex.default(Ex.div(Ex.num(1), Ex.num(0)), Ex.num(42))  # entropy 1

result1, universe1 = run_thermo(clean_expr)
result2, universe2 = run_thermo(recovered_expr)

print(f"Clean 42: value={result1.value}, entropy={universe1.total_entropy}")
print(f"Recovered 42: value={result2.value}, entropy={universe2.total_entropy}")

equiv = MathematicalVerifier.test_noether_theorem(clean_expr, recovered_expr)
print(f"Clean 42 ≡ Recovered 42: {equiv}")
print(f"(Same value but different entropy)")