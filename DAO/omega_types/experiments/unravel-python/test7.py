from unravel_v3 import *

# Test 1: Deep nesting to consume fuel
print("=== FUEL CONSUMPTION TEST ===")
# Build a deeply nested expression
deep_expr = Ex.num(1)
for i in range(10):
    deep_expr = Ex.add(deep_expr, Ex.num(1))

result, universe = run_thermo(deep_expr)
print(f"Deep nesting result: {result.value if hasattr(result, 'value') else result}")
print(f"Entropy: {universe.total_entropy}")
print()

# Test 2: Custom fuel limit
print("=== CUSTOM FUEL LIMIT ===")
# Try with very limited fuel
limited_expr = Ex.num(1)
for i in range(100):  # Much deeper nesting
    limited_expr = Ex.add(limited_expr, Ex.num(1))

# Try with low fuel
result_low, universe_low = run_thermo_with_fuel(10, limited_expr)
print(f"Low fuel (10) result: {result_low}")
print(f"Type: {type(result_low).__name__}")

# Try with high fuel
result_high, universe_high = run_thermo_with_fuel(1000, limited_expr)
print(f"High fuel (1000) result: {result_high}")
print(f"Type: {type(result_high).__name__}")
print()

# Test 3: Let's check the universe object more deeply
print("=== UNIVERSE DETAILS ===")
test_expr = Ex.default(
    Ex.div(Ex.num(10), Ex.num(0)),
    Ex.num(5)
)
result, universe = run_thermo(test_expr)

# Let's see what attributes universe has
print(f"Universe attributes: {[attr for attr in dir(universe) if not attr.startswith('_')]}")
print(f"Total entropy: {universe.total_entropy}")
print(f"Void count: {universe.void_count}")
# Try to access time if it exists
if hasattr(universe, 'time'):
    print(f"Time: {universe.time}")
if hasattr(universe, 'fuel'):
    print(f"Fuel remaining: {universe.fuel}")