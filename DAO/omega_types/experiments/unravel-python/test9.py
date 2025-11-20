from unravel_v3 import *

# Test 1: What happens with negative numbers in division?
print("=== NEGATIVE NUMBERS ===")
neg_div = Ex.div(Ex.num(10), Ex.sub(Ex.num(3), Ex.num(3)))  # 10 / 0 via subtraction
result1, universe1 = run_thermo(neg_div)
print(f"10 / (3-3) = {result1}")
if isinstance(result1, VTVoid):
    print(f"Source: {result1.info.source}")

# Since subtraction saturates at 0, what about:
neg_test = Ex.sub(Ex.num(0), Ex.num(10))  # 0 - 10 in saturating arithmetic
result2, universe2 = run_thermo(neg_test)
print(f"0 - 10 = {result2.value if hasattr(result2, 'value') else result2}")
print()

# Test 2: Mixing types in operations
print("=== TYPE MIXING ===")
# What happens with bool in arithmetic context?
bool_mul = Ex.mul(Ex.bool(False), Ex.num(42))
result3, universe3 = run_thermo(bool_mul)
print(f"False * 42 = {result3}")
if isinstance(result3, VTVoid):
    print(f"Source: {result3.info.source}")

# Bool with default
bool_default = Ex.default(Ex.bool(True), Ex.num(1))
result4, universe4 = run_thermo(bool_default)
print(f"default(True, 1) = {result4}")
print()

# Test 3: Very large numbers
print("=== LARGE NUMBERS ===")
big_calc = Ex.mul(Ex.num(999999), Ex.num(999999))
result5, universe5 = run_thermo(big_calc)
print(f"999999 * 999999 = {result5.value if hasattr(result5, 'value') else result5}")

# Integer overflow test?
huge = Ex.mul(Ex.num(2**30), Ex.num(2**30))
result6, universe6 = run_thermo(huge)
print(f"2^30 * 2^30 = {result6.value if hasattr(result6, 'value') else result6}")
print(f"Type: {type(result6).__name__}")
print()

# Test 4: Can we create custom void?
print("=== EXPLICIT VOID ===")
explicit_void = Ex.void()
result7, universe7 = run_thermo(explicit_void)
print(f"Explicit void: {result7}")
if isinstance(result7, VTVoid):
    print(f"Source: {result7.info.source}")
    print(f"Entropy: {result7.info.entropy}")