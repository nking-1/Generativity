from unravel_v3 import *

# Test 1: Using default to recover from void
print("=== DEFAULT/RECOVERY MECHANISM ===")
safe_div = Ex.default(
    Ex.div(Ex.num(100), Ex.num(0)),  # This will be void
    Ex.num(42)                        # Fallback value
)
result, universe = run_thermo(safe_div)
print(f"Safe division result: {result}")
print(f"Result value: {result.value if hasattr(result, 'value') else 'N/A'}")
print(f"Universe entropy: {universe.total_entropy}")
print(f"Note: We got a real value but entropy shows something went wrong!")
print()

# Test 2: How does void propagate through operations?
print("=== VOID PROPAGATION ===")
propagation = Ex.add(
    Ex.div(Ex.num(10), Ex.num(0)),  # This is void
    Ex.num(5)                        # Normal number
)
result2, universe2 = run_thermo(propagation)
print(f"Void + 5 = {result2}")
print(f"Type: {type(result2).__name__}")
if isinstance(result2, VTVoid):
    print(f"Void info: {result2.info}")
print(f"Universe entropy: {universe2.total_entropy}")
print()

# Test 3: Undefined variable handling
print("=== UNDEFINED VARIABLES ===")
undefined = Ex.variable("ghost_variable")
result3, universe3 = run_thermo(undefined)
print(f"Undefined variable result: {result3}")
print(f"Type: {type(result3).__name__}")
if isinstance(result3, VTVoid):
    print(f"Void source: {result3.info.source}")