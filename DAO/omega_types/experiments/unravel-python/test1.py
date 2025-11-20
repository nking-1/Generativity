from unravel_v3 import *

# First, let's try basic arithmetic that should work normally
simple_calc = Ex.add(Ex.num(10), Ex.num(20))
result, universe = run_thermo(simple_calc)

print(f"Simple addition result: {result}")
print(f"Result type: {type(result).__name__}")
print(f"Result value: {result.value if hasattr(result, 'value') else 'N/A'}")
print(f"Universe entropy: {universe.total_entropy}")
print(f"Universe void count: {universe.void_count}")
print("-" * 40)

# Now let's try division by zero - the classic crash scenario
div_by_zero = Ex.div(Ex.num(100), Ex.num(0))
result2, universe2 = run_thermo(div_by_zero)

print(f"Division by zero result: {result2}")
print(f"Result type: {type(result2).__name__}")
print(f"Has value attr: {hasattr(result2, 'value')}")
print(f"Universe entropy: {universe2.total_entropy}")
print(f"Universe void count: {universe2.void_count}")