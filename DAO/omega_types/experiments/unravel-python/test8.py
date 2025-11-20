from unravel_v3 import *

# Test 1: Simulating a list sum with potential failures
print("=== SAFE LIST PROCESSING ===")
# Simulate summing [10, 20, 0, 30] but dividing each by itself first
# (to simulate validation - div by 0 would be bad data)
sum_expr = Ex.num(0)
values = [(10, 10), (20, 20), (5, 0), (30, 30)]  # (value, divisor)

for val, div in values:
    validated = Ex.div(Ex.num(val), Ex.num(div))  # Validate by dividing
    sum_expr = Ex.add(sum_expr, Ex.default(validated, Ex.num(0)))  # Add with fallback

result, universe = run_thermo(sum_expr)
print(f"Sum result: {result.value if hasattr(result, 'value') else result}")
print(f"Entropy (data quality): {universe.total_entropy}")
print(f"Bad data points: {universe.void_count}")
print()

# Test 2: Chained computations with multiple potential failure points
print("=== CHAINED OPERATIONS ===")
# Simulate: (x / 2) * 3 + (y / 0) with recovery
chained = Ex.let("x", Ex.num(10),
    Ex.let("y", Ex.num(5),
        Ex.add(
            Ex.mul(Ex.div(Ex.variable("x"), Ex.num(2)), Ex.num(3)),  # (x/2)*3 = 15
            Ex.default(
                Ex.div(Ex.variable("y"), Ex.num(0)),  # y/0 = void
                Ex.num(7)  # fallback
            )
        )
    )
)

result, universe = run_thermo(chained)
print(f"Chained result: {result.value if hasattr(result, 'value') else result}")
print(f"Expected: 15 + 7 = 22")
print(f"Entropy: {universe.total_entropy}")
print()

# Test 3: Boolean operations
print("=== BOOLEAN OPERATIONS ===")
bool_true = Ex.bool(True)
bool_false = Ex.bool(False)

result_t, _ = run_thermo(bool_true)
result_f, _ = run_thermo(bool_false)
print(f"True: {result_t}")
print(f"False: {result_f}")

# Can we do arithmetic with bools?
bool_math = Ex.add(Ex.bool(True), Ex.bool(True))
result_bm, universe_bm = run_thermo(bool_math)
print(f"True + True = {result_bm}")
print(f"Type: {type(result_bm).__name__}")