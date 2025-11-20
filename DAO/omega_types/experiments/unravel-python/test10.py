from unravel_v3 import *

# Test 1: Nested recovery - does entropy accumulate?
print("=== NESTED RECOVERY ===")
nested = Ex.default(
    Ex.default(
        Ex.div(Ex.num(1), Ex.num(0)),  # First void
        Ex.div(Ex.num(2), Ex.num(0))   # Second void
    ),
    Ex.num(42)  # Final fallback
)
result, universe = run_thermo(nested)
print(f"Nested default result: {result.value if hasattr(result, 'value') else result}")
print(f"Total entropy: {universe.total_entropy}")
print(f"Void count: {universe.void_count}")
print()

# Test 2: Multiple independent voids
print("=== MULTIPLE INDEPENDENT VOIDS ===")
multi_void = Ex.let("a", Ex.div(Ex.num(1), Ex.num(0)),
    Ex.let("b", Ex.mod(Ex.num(5), Ex.num(0)),
        Ex.let("c", Ex.variable("undefined"),
            Ex.add(
                Ex.default(Ex.variable("a"), Ex.num(10)),
                Ex.add(
                    Ex.default(Ex.variable("b"), Ex.num(20)),
                    Ex.default(Ex.variable("c"), Ex.num(30))
                )
            )
        )
    )
)
result2, universe2 = run_thermo(multi_void)
print(f"Multi-void result: {result2.value if hasattr(result2, 'value') else result2}")
print(f"Expected: 10 + 20 + 30 = 60")
print(f"Total entropy: {universe2.total_entropy}")
print(f"Void count: {universe2.void_count}")
print()

# Test 3: Time tracking
print("=== TIME PROGRESSION ===")
timed = Ex.let("step1", Ex.div(Ex.num(1), Ex.num(0)),
    Ex.let("step2", Ex.add(Ex.num(5), Ex.num(5)),
        Ex.let("step3", Ex.mod(Ex.num(7), Ex.num(0)),
            Ex.num(100)
        )
    )
)
result3, universe3 = run_thermo(timed)
print(f"Result: {result3.value if hasattr(result3, 'value') else result3}")

# Let's manually check what time_step does
if hasattr(universe3, 'initial'):
    print(f"Initial universe: {universe3.initial}")
if hasattr(universe3, 'time_step'):
    print(f"Current time step: {universe3.time_step}")
print()

# Test 4: Conservation law deeper test
print("=== CONSERVATION LAW VERIFICATION ===")
# Create same final value through different paths
path1 = Ex.num(100)  # Direct
path2 = Ex.default(Ex.div(Ex.num(1), Ex.num(0)), Ex.num(100))  # Through void

result_p1, universe_p1 = run_thermo(path1)
result_p2, universe_p2 = run_thermo(path2)

print(f"Path 1 (direct): value={result_p1.value}, entropy={universe_p1.total_entropy}")
print(f"Path 2 (void recovery): value={result_p2.value}, entropy={universe_p2.total_entropy}")
print(f"Same value? {result_p1.value == result_p2.value}")
print(f"Same entropy? {universe_p1.total_entropy == universe_p2.total_entropy}")