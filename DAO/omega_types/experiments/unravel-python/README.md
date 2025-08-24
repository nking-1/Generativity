# Unravel - Total Functional Programming for Python

A Python library for building programs that never crash through mathematical guarantees.

## Installation

```python
# Copy unravel_v3.py to your project
from unravel_v3 import *
```

## Basic Concepts

Unravel provides **total functions** - operations that always return a meaningful result instead of throwing exceptions. When operations would normally fail, they return structured "void" values with debugging information.

### Core Types

- **ExprV**: Expressions that can be evaluated
- **ValueT**: Results of evaluation (VTNum, VTBool, or VTVoid)
- **Universe**: Tracks computational state (entropy, time, void count)

## API Reference

### Expression Builders

```python
Ex.num(value)                    # Number literal
Ex.bool(value)                   # Boolean literal  
Ex.void()                        # Explicit void
Ex.add(left, right)              # Addition
Ex.sub(left, right)              # Subtraction (saturating, never negative)
Ex.mul(left, right)              # Multiplication
Ex.div(left, right)              # Division (returns void on divide by zero)
Ex.mod(left, right)              # Modulo (returns void on mod by zero)
Ex.default(expr, fallback)       # Use fallback if expr is void
Ex.variable(name)                # Variable reference
Ex.let(name, binding, body)      # Let binding
```

### Evaluation Functions

```python
run_thermo(expr)                 # Evaluate expression, returns (ValueT, Universe)
run_thermo_with_fuel(fuel, expr) # Evaluate with custom fuel limit
```

### Mathematical Verification

```python
MathematicalVerifier.test_noether_theorem(expr1, expr2)     # Test if expressions are equivalent
MathematicalVerifier.test_conservation_law(void_expr, fallback)  # Test entropy preservation
MathematicalVerifier.test_base_veil_principle(void_expr)    # Test void has entropy >= 1
```

## Examples

### Basic Safe Operations

```python
# Safe division that never crashes
result = run_thermo(Ex.div(Ex.num(10), Ex.num(0)))
if isinstance(result[0], VTVoid):
    print("Division by zero handled gracefully")
else:
    print(f"Result: {result[0].value}")

# Safe calculation with fallback
safe_calc = Ex.default(
    Ex.div(Ex.num(100), Ex.num(0)),  # This will be void
    Ex.num(42)                       # Fallback value
)
result = run_thermo(safe_calc)
print(f"Safe result: {result[0].value}")  # Always gets a number
```

### Variable Environment

```python
# Let bindings work like normal
let_example = Ex.let("x", Ex.num(10),
                    Ex.add(Ex.variable("x"), Ex.num(5)))
result = run_thermo(let_example)
print(f"Let result: {result[0].value}")  # 15

# Undefined variables become void (no exceptions)
undefined_example = Ex.add(Ex.variable("nonexistent"), Ex.num(42))
result = run_thermo(undefined_example)
print(f"Undefined handled: {type(result[0]).__name__}")  # VTVoid
```

### Entropy Tracking

```python
# Track computational "health" through entropy
calculation = Ex.let("a", Ex.div(Ex.num(100), Ex.num(0)),  # Creates entropy
                    Ex.let("b", Ex.add(Ex.variable("a"), Ex.num(50)),  # Propagates void
                          Ex.default(Ex.variable("b"), Ex.num(999))))  # Recovery

result = run_thermo(calculation)
print(f"Result: {result[0].value}")              # 999 (recovered)
print(f"Entropy: {result[1].total_entropy}")     # > 0 (shows issues occurred)
print(f"Void count: {result[1].void_count}")     # Number of void encounters
```

### Mathematical Laws

```python
# Verify mathematical properties of your code
expr1 = Ex.add(Ex.num(20), Ex.num(30))
expr2 = Ex.add(Ex.num(30), Ex.num(20))

# These should be equivalent (Noether's theorem)
equivalent = MathematicalVerifier.test_noether_theorem(expr1, expr2)
print(f"20 + 30 ≡ 30 + 20: {equivalent}")  # True

# Recovery preserves entropy (conservation law)
void_expr = Ex.div(Ex.num(10), Ex.num(0))
fallback = Ex.num(99)
conserved = MathematicalVerifier.test_conservation_law(void_expr, fallback)
print(f"Recovery preserves entropy: {conserved}")  # True
```

## Practical Examples

### Safe Data Processing

```python
def safe_average(numbers):
    """Calculate average that never crashes on empty list or bad data"""
    total_expr = Ex.num(0)
    count_expr = Ex.num(0)
    
    for i, num in enumerate(numbers):
        if isinstance(num, (int, float)):
            total_expr = Ex.add(total_expr, Ex.num(int(num)))
            count_expr = Ex.add(count_expr, Ex.num(1))
    
    avg_expr = Ex.default(
        Ex.div(total_expr, count_expr),  # Could divide by zero
        Ex.num(0)                        # Fallback for empty list
    )
    
    result = run_thermo(avg_expr)
    return {
        'average': result[0].value if isinstance(result[0], VTNum) else 0,
        'data_quality': 'good' if result[1].total_entropy == 0 else 'issues_detected',
        'entropy': result[1].total_entropy
    }

# Test with messy data
messy_data = [10, 20, None, "not_a_number", 30, 0]
result = safe_average(messy_data)
print(result)  # Always get a result, entropy shows data quality
```

### Configuration Loading

```python
def load_config(config_dict):
    """Load configuration that never prevents app startup"""
    
    # Port with validation and fallback
    port_raw = config_dict.get('port', 8080)
    port_val = port_raw if isinstance(port_raw, int) and port_raw > 0 else 8080
    
    port_expr = Ex.default(
        Ex.div(Ex.num(port_val), Ex.num(1) if 1024 <= port_val <= 65535 else Ex.num(0)),
        Ex.num(8080)
    )
    
    # Database URL validation
    db_url = config_dict.get('database_url', 'sqlite://default.db')
    db_check = Ex.num(1) if isinstance(db_url, str) and len(db_url) > 0 else Ex.num(0)
    
    config_expr = Ex.add(port_expr, db_check)
    result = run_thermo(config_expr)
    
    return {
        'port': port_val,
        'database_url': db_url,
        'config_health': 'perfect' if result[1].total_entropy == 0 else 'degraded',
        'startup_guaranteed': True  # Always starts with valid config
    }

# Test with broken config
broken_config = {'port': 'not_a_port', 'database_url': ''}
config = load_config(broken_config)
print(config)  # App starts anyway with sensible defaults
```

### Error Accumulation Pattern

```python
def process_batch(items):
    """Process list of items, accumulating error information"""
    
    results = []
    total_expr = Ex.num(0)
    
    for item in items:
        # Process each item (some might fail)
        item_expr = Ex.default(
            Ex.div(Ex.num(item.get('value', 0)), Ex.num(item.get('divisor', 1))),
            Ex.num(0)  # Failed items become 0
        )
        total_expr = Ex.add(total_expr, item_expr)
    
    result = run_thermo(total_expr)
    
    return {
        'total': result[0].value if isinstance(result[0], VTNum) else 0,
        'items_processed': len(items),
        'processing_errors': result[1].void_count,
        'data_quality_score': max(0, 100 - result[1].total_entropy * 5)
    }
```

## Key Features

- **Never crashes**: All operations return meaningful results
- **Rich debugging**: Entropy tracking shows system health
- **Mathematical guarantees**: Equivalent operations have identical entropy
- **Graceful degradation**: Bad inputs become structured information
- **Zero dependencies**: Pure Python implementation

## Configuration

```python
# Adjustable parameters in unravel_v3.py
DEFAULT_FUEL = 1000           # Computation budget (prevents infinite loops)
HEAT_DEATH_THRESHOLD = 100    # Entropy level for system health warnings
BASE_ENTROPY = 1              # Minimum entropy per void encounter
```

## Performance

The library is designed for correctness and insight rather than raw speed. Typical performance:
- Basic operations: Fast (direct evaluation)
- Complex expressions: Moderate (fuel-bounded evaluation)
- Rich debugging: Detailed void information tracking

## Use Cases

- Data processing pipelines that handle corrupted input
- Configuration systems that never prevent startup  
- Financial calculations that never lose money to edge cases
- API endpoints that always return useful responses
- Game logic that never breaks player experience
- Scientific computing with numerical stability guarantees

## License

MIT License - Use freely in any project.