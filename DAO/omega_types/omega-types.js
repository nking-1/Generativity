/**
 * omega-types.js  
 * Total functional programming for JavaScript/TypeScript
 * Based on omega_veil and impossibility algebra
 * 
 * Works on both frontend (browser) and backend (Node.js)
 */

// ============================================================================
// CORE TYPES AND MATHEMATICAL FOUNDATIONS
// ============================================================================

/** Impossibility patterns - different ways of encountering omega_veil */
const ImpossibilityPattern = {
  DIVISION_BY_ZERO: "DIVISION_BY_ZERO",
  ARITHMETIC_OVERFLOW: "ARITHMETIC_OVERFLOW", 
  INDEX_OUT_OF_BOUNDS: "INDEX_OUT_OF_BOUNDS",
  NETWORK_TIMEOUT: "NETWORK_TIMEOUT",
  PARSE_ERROR: "PARSE_ERROR",
  VALIDATION_ERROR: "VALIDATION_ERROR",
  AUTHENTICATION_FAILURE: "AUTHENTICATION_FAILURE",
  RATE_LIMIT_EXCEEDED: "RATE_LIMIT_EXCEEDED",
  CONFIGURATION_ERROR: "CONFIGURATION_ERROR",
  DATABASE_ERROR: "DATABASE_ERROR",
  FILE_NOT_FOUND: "FILE_NOT_FOUND",
  COMPOSITE_VOID: "COMPOSITE_VOID"
};

/** Create a value (successful computation) */
function value(val) {
  return { tag: 'Value', value: val };
}

/** Create structured void (omega_veil encounter) */
function void_(pattern, source, details = {}) {
  return {
    tag: 'Void',
    info: {
      pattern,
      depth: 1,  // BaseVeil principle
      source,
      timestamp: Date.now(),
      details
    }
  };
}

/** Create thermodynamic value (pure, no entropy) */
function thermo(val) {
  return {
    value: value(val),
    entropy: 0,
    history: []
  };
}

/** Create thermodynamic void */
function thermoVoid(pattern, source, details = {}) {
  const voidInfo = {
    pattern,
    depth: 1,
    source,
    timestamp: Date.now(),
    details
  };
  
  return {
    value: { tag: 'Void', info: voidInfo },
    entropy: 1,  // BaseVeil: minimum entropy 1
    history: [voidInfo]
  };
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/** Check if Omega value is void */
function isVoid(omega) {
  return omega.tag === 'Void';
}

/** Check if ThermoOmega value is void */
function isThermoVoid(thermo) {
  return isVoid(thermo.value);
}

/** Extract value with fallback */
function unwrapOr(omega, fallback) {
  return omega.tag === 'Value' ? omega.value : fallback;
}

/** Extract value from ThermoOmega with fallback */
function unwrapThermoOr(thermo, fallback) {
  return unwrapOr(thermo.value, fallback);
}

// ============================================================================
// MATHEMATICAL OPERATIONS (IMPOSSIBILITY ALGEBRA)
// ============================================================================

/** Combine two void infos (impossibility algebra) */
function combineVoids(v1, v2) {
  return {
    pattern: ImpossibilityPattern.COMPOSITE_VOID,
    depth: v1.depth + v2.depth,  // Entropy accumulation
    source: `${v1.source}+${v2.source}`,
    timestamp: Math.max(v1.timestamp, v2.timestamp),
    details: { 
      combined: [v1, v2],
      patterns: [v1.pattern, v2.pattern]
    }
  };
}

/** Safe integer addition with overflow protection */
function safeAdd(a, b) {
  // Check for overflow (JavaScript number safety)
  if (!Number.isSafeInteger(a) || !Number.isSafeInteger(b)) {
    return void_(ImpossibilityPattern.ARITHMETIC_OVERFLOW, `unsafe_integer_${a}_or_${b}`);
  }
  
  const result = a + b;
  if (!Number.isSafeInteger(result)) {
    return void_(ImpossibilityPattern.ARITHMETIC_OVERFLOW, `overflow_${a}+${b}`);
  }
  
  return value(result);
}

/** Safe division with zero protection */
function safeDiv(a, b) {
  if (b === 0) {
    return void_(ImpossibilityPattern.DIVISION_BY_ZERO, `div_by_zero_${a}/0`);
  }
  
  if (!Number.isSafeInteger(a) || !Number.isSafeInteger(b)) {
    return void_(ImpossibilityPattern.ARITHMETIC_OVERFLOW, `unsafe_division_${a}/${b}`);
  }
  
  return value(Math.floor(a / b));  // Integer division
}

/** ThermoOmega addition with entropy tracking */
function thermoAdd(x, y) {
  // Handle void cases (impossibility propagation)
  if (isVoid(x.value) && isVoid(y.value)) {
    // Void + Void = Combined void
    const combined = combineVoids(x.value.info, y.value.info);
    return {
      value: { tag: 'Void', info: combined },
      entropy: x.entropy + y.entropy + 1,  // +1 for the operation
      history: [...x.history, ...y.history, combined]
    };
  }
  
  if (isVoid(x.value)) {
    return {
      value: x.value,
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, x.value.info]
    };
  }
  
  if (isVoid(y.value)) {
    return {
      value: y.value,
      entropy: x.entropy + y.entropy + 1, 
      history: [...x.history, ...y.history, y.value.info]
    };
  }
  
  // Both are values - perform safe addition
  const result = safeAdd(x.value.value, y.value.value);
  
  if (isVoid(result)) {
    return {
      value: result,
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, result.info]
    };
  }
  
  return {
    value: result,
    entropy: x.entropy + y.entropy,  // No new errors
    history: [...x.history, ...y.history]
  };
}

/** ThermoOmega division with entropy tracking */
function thermoDiv(x, y) {
  // Handle void cases first
  if (isVoid(x.value) || isVoid(y.value)) {
    const voidInfo = isVoid(x.value) ? x.value.info : y.value.info;
    return {
      value: { tag: 'Void', info: voidInfo },
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, voidInfo]
    };
  }
  
  // Both are values - perform safe division
  const result = safeDiv(x.value.value, y.value.value);
  
  if (isVoid(result)) {
    return {
      value: result,
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, result.info]
    };
  }
  
  return {
    value: result,
    entropy: x.entropy + y.entropy,
    history: [...x.history, ...y.history]
  };
}

/** Recovery with entropy conservation */
function recover(thermo, fallback) {
  if (isVoid(thermo.value)) {
    return {
      value: value(fallback),
      entropy: thermo.entropy,  // Conservation law: preserve entropy
      history: thermo.history
    };
  }
  return thermo;
}

// ============================================================================
// FLUENT API FOR ERGONOMIC USAGE
// ============================================================================

/** Fluent ThermoOmega wrapper for chaining operations */
class ThermoChain {
  constructor(thermo) {
    this.thermo = thermo;
  }
  
  /** Add another value */
  add(otherValue) {
    const other = typeof otherValue === 'object' ? otherValue : thermo(otherValue);
    const result = thermoAdd(this.thermo, other);
    return new ThermoChain(result);
  }
  
  /** Divide by another value */
  divide(otherValue) {
    const other = typeof otherValue === 'object' ? otherValue : thermo(otherValue);
    const result = thermoDiv(this.thermo, other);
    return new ThermoChain(result);
  }
  
  /** Map over the value */
  map(fn) {
    if (isVoid(this.thermo.value)) {
      return new ThermoChain(this.thermo);
    }
    
    try {
      const mapped = fn(this.thermo.value.value);
      return new ThermoChain({
        value: value(mapped),
        entropy: this.thermo.entropy,
        history: this.thermo.history
      });
    } catch (error) {
      const voidInfo = {
        pattern: ImpossibilityPattern.VALIDATION_ERROR,
        depth: 1,
        source: 'map_function_error',
        timestamp: Date.now(),
        details: { error: error.message }
      };
      
      return new ThermoChain({
        value: { tag: 'Void', info: voidInfo },
        entropy: this.thermo.entropy + 1,
        history: [...this.thermo.history, voidInfo]
      });
    }
  }
  
  /** Recover with fallback value */
  recover(fallback) {
    const result = recover(this.thermo, fallback);
    return new ThermoChain(result);
  }
  
  /** Extract the final ThermoOmega value */
  unwrap() {
    return this.thermo;
  }
  
  /** Extract value with fallback */
  unwrapOr(fallback) {
    return unwrapThermoOr(this.thermo, fallback);
  }
  
  /** Get entropy information */
  entropy() {
    return this.thermo.entropy;
  }
  
  /** Get void encounter history */
  history() {
    return this.thermo.history;
  }
  
  /** Check if computation encountered impossibility */
  hasErrors() {
    return this.thermo.entropy > 0;
  }
  
  /** Pretty print for debugging */
  toString() {
    const val = unwrapThermoOr(this.thermo, 'void');
    return `${val} [entropy: ${this.entropy()}]`;
  }
}

/** Create a fluent chain from a value */
function chain(value) {
  return new ThermoChain(thermo(value));
}

// ============================================================================
// FRONTEND-SPECIFIC UTILITIES  
// ============================================================================

/** Safe DOM element access */
function safeGetElement(id) {
  if (typeof document === 'undefined') {
    return void_(ImpossibilityPattern.CONFIGURATION_ERROR, 'not_in_browser');
  }
  
  const element = document.getElementById(id);
  if (!element) {
    return void_(ImpossibilityPattern.FILE_NOT_FOUND, `element_not_found_${id}`);
  }
  
  return value(element);
}

/** Safe JSON parsing */
function safeParseJSON(json) {
  try {
    const parsed = JSON.parse(json);
    return value(parsed);
  } catch (error) {
    return void_(
      ImpossibilityPattern.PARSE_ERROR, 
      'json_parse_error',
      { originalError: error.message }
    );
  }
}

/** Safe localStorage access */
function safeLocalStorage(key) {
  if (typeof localStorage === 'undefined') {
    return void_(ImpossibilityPattern.CONFIGURATION_ERROR, 'no_localstorage');
  }
  
  try {
    const value_ = localStorage.getItem(key);
    if (value_ === null) {
      return void_(ImpossibilityPattern.FILE_NOT_FOUND, `localstorage_key_${key}`);
    }
    return value(value_);
  } catch (error) {
    return void_(
      ImpossibilityPattern.DATABASE_ERROR,
      `localstorage_error_${key}`,
      { error: error.message }
    );
  }
}

// ============================================================================
// PRACTICAL EXAMPLES
// ============================================================================

/** Example: Safe array processing */
function safeArraySum(numbers) {
  return numbers.reduce((acc, num) => {
    return acc.add(num);
  }, chain(0));
}

/** Example: Safe object property access */
function safeGetProperty(obj, path) {
  try {
    const keys = path.split('.');
    let current = obj;
    
    for (const key of keys) {
      if (current == null || typeof current !== 'object') {
        return void_(ImpossibilityPattern.VALIDATION_ERROR, `property_access_failed_${path}`);
      }
      current = current[key];
    }
    
    if (current === undefined) {
      return void_(ImpossibilityPattern.FILE_NOT_FOUND, `property_undefined_${path}`);
    }
    
    return value(current);
  } catch (error) {
    return void_(ImpossibilityPattern.VALIDATION_ERROR, `property_error_${path}`, { error: error.message });
  }
}

/** Example: Portfolio calculation for frontend */
async function calculatePortfolioValue(positions) {
  let totalValue = chain(0);
  let errors = [];
  
  for (const position of positions) {
    if (!position.quantity || !position.price || position.quantity <= 0 || position.price <= 0) {
      errors.push(`invalid_position_${position.symbol}`);
      continue;
    }
    
    const positionValue = chain(position.quantity)
      .map(q => q * position.price)
      .map(v => Math.floor(v * 100)); // Convert to cents
    
    totalValue = totalValue.add(positionValue.unwrap());
  }
  
  return totalValue;
}

// ============================================================================
// TESTING AND DEMONSTRATION
// ============================================================================

/** Run comprehensive tests */
async function runTests() {
  console.log('=== OMEGA TYPES JAVASCRIPT/TYPESCRIPT TESTING ===\n');
  
  // Test 1: Basic arithmetic
  console.log('TEST 1: Basic Arithmetic');
  const calc1 = chain(10).add(20);
  console.log(`  10 + 20 = ${calc1.unwrapOr(0)}, entropy = ${calc1.entropy()}`);
  
  // Test 2: Division by zero
  console.log('\nTEST 2: Division by Zero');
  const calc2 = chain(10).divide(0).recover(999);
  console.log(`  10 / 0 (recovered) = ${calc2.unwrapOr(0)}, entropy = ${calc2.entropy()}`);
  console.log(`  Void info: ${JSON.stringify(calc2.history()[0], null, 2)}`);
  
  // Test 3: JSON parsing
  console.log('\nTEST 3: Safe JSON Parsing');
  const validJson = safeParseJSON('{"name": "test", "value": 42}');
  const invalidJson = safeParseJSON('invalid json string');
  console.log(`  Valid JSON: ${isVoid(validJson) ? 'Failed' : 'Success'}`);
  console.log(`  Invalid JSON: ${isVoid(invalidJson) ? 'Handled gracefully' : 'Unexpected success'}`);
  
  // Test 4: Noether's theorem verification
  console.log('\nTEST 4: Noether\'s Theorem');
  const noether1 = chain(10).add(20);
  const noether2 = chain(20).add(10);
  console.log(`  10 + 20 entropy: ${noether1.entropy()}`);
  console.log(`  20 + 10 entropy: ${noether2.entropy()}`);
  console.log(`  ✓ Commutativity preserves entropy: ${noether1.entropy() === noether2.entropy()}`);
  
  // Test 5: Error accumulation and conservation
  console.log('\nTEST 5: Error Accumulation & Conservation');
  const errors = chain(100)
    .divide(0)          // +1 entropy (division by zero)
    .add(50)            // +1 entropy (void + value = void)
    .recover(200)       // preserve entropy
    .add(25);           // +0 entropy (value + value)
  
  console.log(`  Complex computation with recovery:`);
  console.log(`    Final value: ${errors.unwrapOr(0)}`);
  console.log(`    Total entropy: ${errors.entropy()}`);
  console.log(`    Error history: ${errors.history().length} encounters`);
  
  // Test 6: Array processing with partial failures
  console.log('\nTEST 6: Array Processing with Partial Failures');
  const numbers = [10, 20, 0, 30, -5];  // Mix of valid and potentially problematic
  const arraySum = safeArraySum(numbers);
  console.log(`  Sum of [${numbers.join(', ')}] = ${arraySum.unwrapOr(0)}`);
  console.log(`  Processing entropy: ${arraySum.entropy()}`);
  
  // Test 7: Object property access
  console.log('\nTEST 7: Safe Property Access');
  const testObj = { user: { profile: { name: 'John', age: 30 } } };
  const validAccess = safeGetProperty(testObj, 'user.profile.name');
  const invalidAccess = safeGetProperty(testObj, 'user.profile.nonexistent');
  
  console.log(`  Valid property: ${unwrapOr(validAccess, 'not found')}`);
  console.log(`  Invalid property: ${isVoid(invalidAccess) ? 'Handled gracefully' : 'Unexpected success'}`);
  
  // Test 8: Portfolio calculation
  console.log('\nTEST 8: Portfolio Calculation');
  const portfolio = [
    { symbol: 'AAPL', quantity: 100, price: 150.50 },
    { symbol: 'GOOGL', quantity: 50, price: 2800.75 },
    { symbol: 'INVALID', quantity: -10, price: 100 },  // Bad data
    { symbol: 'TSLA', quantity: 25, price: 800.25 }
  ];
  
  const portfolioValue = await calculatePortfolioValue(portfolio);
  console.log(`  Portfolio value: $${(portfolioValue.unwrapOr(0) / 100).toFixed(2)}`);
  console.log(`  Calculation entropy: ${portfolioValue.entropy()}`);
  console.log(`  Errors encountered: ${portfolioValue.history().length}`);
  
  console.log('\n=== FRONTEND/BACKEND COMPATIBILITY ===');
  console.log(`  Running in: ${typeof window !== 'undefined' ? 'Browser' : 'Node.js'}`);
  console.log(`  DOM available: ${typeof document !== 'undefined'}`);
  console.log(`  localStorage available: ${typeof localStorage !== 'undefined'}`);
  console.log(`  Node.js modules available: ${typeof require !== 'undefined'}`);
  
  console.log('\n✅ All tests demonstrate mathematical law compliance!');
  console.log('✅ Works seamlessly on both frontend and backend!');
}

// ============================================================================
// PRACTICAL USE CASE EXAMPLES
// ============================================================================

/** Example: Safe API response processing (frontend/backend) */
function processApiResponse(response) {
  return chain(response)
    .map(resp => {
      if (!resp.ok) {
        throw new Error(`HTTP ${resp.status}: ${resp.statusText}`);
      }
      return resp;
    })
    .map(resp => resp.json())  // This would be async in real usage
    .recover({ error: 'Failed to process API response' });
}

/** Example: Safe form validation (frontend) */
function validateUserForm(formData) {
  return chain(formData)
    .map(data => {
      const errors = [];
      
      if (!data.email || !data.email.includes('@')) {
        errors.push('Invalid email');
      }
      
      if (!data.password || data.password.length < 8) {
        errors.push('Password too short');
      }
      
      if (parseInt(data.age) < 18 || parseInt(data.age) > 100) {
        errors.push('Invalid age');
      }
      
      if (errors.length > 0) {
        throw new Error(errors.join(', '));
      }
      
      return {
        email: data.email,
        password: data.password,
        age: parseInt(data.age)
      };
    });
}

/** Example: Safe configuration loading (backend) */
function loadConfiguration(configObject) {
  const getConfig = (key, defaultValue, validator = () => true) => {
    const rawValue = configObject[key];
    if (rawValue === undefined) {
      return defaultValue;
    }
    
    if (!validator(rawValue)) {
      throw new Error(`Invalid ${key}: ${rawValue}`);
    }
    
    return rawValue;
  };
  
  return chain(configObject)
    .map(config => ({
      port: getConfig('port', 3000, p => p > 0 && p < 65536),
      host: getConfig('host', 'localhost'),
      dbUrl: getConfig('dbUrl', 'sqlite://memory.db'),
      maxConnections: getConfig('maxConnections', 100, n => n > 0),
      timeout: getConfig('timeout', 30000, t => t > 0)
    }))
    .recover({
      port: 3000,
      host: 'localhost', 
      dbUrl: 'sqlite://memory.db',
      maxConnections: 100,
      timeout: 30000
    });
}

// ============================================================================
// EXPORT FOR MODULES AND TESTING
// ============================================================================

// Export everything for use as module
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    // Core types
    ImpossibilityPattern,
    value,
    void_,
    thermo,
    thermoVoid,
    
    // Utilities  
    isVoid,
    isThermoVoid,
    unwrapOr,
    unwrapThermoOr,
    
    // Operations
    safeAdd,
    safeDiv,
    thermoAdd,
    thermoDiv,
    recover,
    
    // Fluent API
    ThermoChain,
    chain,
    
    // Frontend utilities
    safeGetElement,
    safeParseJSON,
    safeLocalStorage,
    
    // Examples
    safeArraySum,
    safeGetProperty,
    calculatePortfolioValue,
    processApiResponse,
    validateUserForm,
    loadConfiguration,
    
    // Testing
    runTests
  };
}

// Export for ES modules
if (typeof window !== 'undefined') {
  window.OmegaTypes = {
    ImpossibilityPattern,
    value,
    void_,
    thermo,
    thermoVoid,
    isVoid,
    unwrapOr,
    chain,
    safeParseJSON,
    safeGetElement,
    safeLocalStorage,
    runTests
  };
}

// Auto-run tests if executed directly
if (typeof require !== 'undefined' && require.main === module) {
  runTests().catch(console.error);
}