from unravel_v3 import *

# Test 1: Variable shadowing
print("=== VARIABLE SHADOWING ===")
shadow = Ex.let("x", Ex.num(10),
    Ex.let("x", Ex.num(20),  # Shadow outer x
        Ex.add(Ex.variable("x"), Ex.variable("x"))
    )
)
result, universe = run_thermo(shadow)
print(f"Shadowed x + x = {result.value if hasattr(result, 'value') else result}")
print(f"Expected: 20 + 20 = 40")
print()

# Test 2: Accessing outer scope
print("=== NESTED SCOPE ACCESS ===")
nested_scope = Ex.let("outer", Ex.num(100),
    Ex.let("inner", Ex.num(10),
        Ex.add(Ex.variable("outer"), Ex.variable("inner"))
    )
)
result2, universe2 = run_thermo(nested_scope)
print(f"outer + inner = {result2.value if hasattr(result2, 'value') else result2}")
print()

# Test 3: Complex void tracking
print("=== VOID GENEALOGY ===")
genealogy = Ex.let("grandparent", Ex.div(Ex.num(1), Ex.num(0)),
    Ex.let("parent", Ex.add(Ex.variable("grandparent"), Ex.num(10)),
        Ex.let("child", Ex.mul(Ex.variable("parent"), Ex.num(2)),
            Ex.default(Ex.variable("child"), Ex.num(999))
        )
    )
)
result3, universe3 = run_thermo(genealogy)
print(f"Final result: {result3.value if hasattr(result3, 'value') else result3}")
print(f"Entropy: {universe3.total_entropy}")
print(f"Note: Single void source propagated through 3 generations")
print()

# Test 4: What's the maximum useful entropy before hitting HEAT_DEATH?
print("=== ENTROPY LIMITS ===")
print("Building expression with 20 sequential voids...")
mega_entropy = Ex.num(0)
for i in range(20):
    mega_entropy = Ex.add(
        mega_entropy,
        Ex.default(Ex.div(Ex.num(1), Ex.num(0)), Ex.num(1))
    )

result4, universe4 = run_thermo(mega_entropy)
print(f"Result: {result4.value if hasattr(result4, 'value') else result4}")
print(f"Total entropy: {universe4.total_entropy}")
print(f"Status: {'Still running!' if isinstance(result4, (VTNum, VTBool)) else 'Failed'}")

# Based on README, HEAT_DEATH_THRESHOLD = 100
if universe4.total_entropy > 50:
    print(f"WARNING: System health critical (>{50} entropy)")