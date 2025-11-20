from unravel_v3 import *

# Test 1: Can we inspect void propagation chains?
print("=== VOID PROPAGATION CHAIN ===")
chain = Ex.add(
    Ex.mul(
        Ex.div(Ex.num(10), Ex.num(0)),  # Initial void
        Ex.num(5)
    ),
    Ex.num(100)
)
result, universe = run_thermo(chain)
print(f"Result: {result}")
if isinstance(result, VTVoid):
    info = result.info
    print(f"Entropy: {info.entropy}")
    print(f"Time: {info.time_created}")
    print(f"Source type: {type(info.source).__name__}")
    
    # Check if it's a propagation
    if hasattr(info.source, 'parent1'):
        print(f"  Parent1: {info.source.parent1}")
    if hasattr(info.source, 'parent2'):
        print(f"  Parent2: {info.source.parent2}")
print()

# Test 2: Maximum entropy test
print("=== HIGH ENTROPY COMPUTATION ===")
# Create a computation with lots of failures
high_entropy = Ex.num(0)
for i in range(5):
    void_part = Ex.default(
        Ex.div(Ex.num(i), Ex.num(0)),
        Ex.num(1)
    )
    high_entropy = Ex.add(high_entropy, void_part)

result2, universe2 = run_thermo(high_entropy)
print(f"Result: {result2.value if hasattr(result2, 'value') else result2}")
print(f"Total entropy: {universe2.total_entropy}")
print(f"Void count: {universe2.void_count}")
print(f"Health assessment: {'Critical' if universe2.total_entropy > 3 else 'Degraded' if universe2.total_entropy > 0 else 'Healthy'}")
print()

# Test 3: Zero edge cases
print("=== ZERO EDGE CASES ===")
zero_mul = Ex.mul(Ex.num(0), Ex.div(Ex.num(1), Ex.num(0)))
result3, universe3 = run_thermo(zero_mul)
print(f"0 * (1/0) = {result3}")
print(f"Type: {type(result3).__name__}")

zero_div_valid = Ex.div(Ex.num(0), Ex.num(5))
result4, universe4 = run_thermo(zero_div_valid)
print(f"0 / 5 = {result4.value if hasattr(result4, 'value') else result4}")
print()

# Test 4: Build a "safe calculator" function
print("=== SAFE CALCULATOR PATTERN ===")
def safe_calculate(a, b, op):
    """Build a safe calculation expression"""
    if op == '+':
        expr = Ex.add(Ex.num(a), Ex.num(b))
    elif op == '-':
        expr = Ex.sub(Ex.num(a), Ex.num(b))
    elif op == '*':
        expr = Ex.mul(Ex.num(a), Ex.num(b))
    elif op == '/':
        expr = Ex.default(
            Ex.div(Ex.num(a), Ex.num(b)),
            Ex.num(float('inf'))  # Use infinity as sentinel
        )
    elif op == '%':
        expr = Ex.default(
            Ex.mod(Ex.num(a), Ex.num(b)),
            Ex.num(0)
        )
    else:
        expr = Ex.void()
    
    result, universe = run_thermo(expr)
    
    return {
        'result': result.value if hasattr(result, 'value') else None,
        'success': isinstance(result, VTNum),
        'entropy': universe.total_entropy,
        'health': 'healthy' if universe.total_entropy == 0 else 'degraded'
    }

# Test the calculator
ops = [(10, 5, '+'), (10, 5, '-'), (10, 0, '/'), (17, 5, '%'), (10, 5, '**')]
for a, b, op in ops:
    calc_result = safe_calculate(a, b, op)
    print(f"{a} {op} {b} = {calc_result}")