from unravel_v3 import *

# Test 1: Simple let binding that works
print("=== WORKING LET BINDING ===")
simple_let = Ex.let("x", Ex.num(10),
                   Ex.mul(Ex.variable("x"), Ex.num(3)))
result, universe = run_thermo(simple_let)
print(f"Let result: {result}")
print(f"Value: {result.value if hasattr(result, 'value') else 'N/A'}")
print(f"Entropy: {universe.total_entropy}")
print()

# Test 2: Let binding with void value
print("=== LET BINDING WITH VOID ===")
void_let = Ex.let("bad", Ex.div(Ex.num(1), Ex.num(0)),  # bad = void
                  Ex.add(Ex.variable("bad"), Ex.num(100)))  # bad + 100
result2, universe2 = run_thermo(void_let)
print(f"Result: {result2}")
print(f"Type: {type(result2).__name__}")
print(f"Entropy: {universe2.total_entropy}")
print(f"Void count: {universe2.void_count}")
print()

# Test 3: Multi-step computation with recovery
print("=== MULTI-STEP WITH RECOVERY ===")
complex_expr = Ex.let("a", Ex.div(Ex.num(100), Ex.num(0)),      # a = void
                     Ex.let("b", Ex.add(Ex.variable("a"), Ex.num(50)),  # b = void  
                           Ex.let("c", Ex.default(Ex.variable("b"), Ex.num(999)),  # c = 999
                                 Ex.mul(Ex.variable("c"), Ex.num(2)))))  # c * 2
result3, universe3 = run_thermo(complex_expr)
print(f"Final result: {result3}")
print(f"Value: {result3.value if hasattr(result3, 'value') else 'N/A'}")
print(f"Total entropy: {universe3.total_entropy}")
print(f"Void count: {universe3.void_count}")
print(f"Note: We recovered and got a result, but entropy tracks the full history!")