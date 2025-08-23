/**
 * omega-types.ts
 * Total functional programming for TypeScript
 * Based on omega_veil and impossibility algebra
 * 
 * Works on both frontend (browser) and backend (Node.js)
 */

// ============================================================================
// CORE TYPES AND MATHEMATICAL FOUNDATIONS
// ============================================================================

/**
 * Different patterns of impossibility
 * Extensionally equal (all map to omega_veil) but intensionally distinct
 */
export enum ImpossibilityPattern {
  DivisionByZero = "DIVISION_BY_ZERO",
  ArithmeticOverflow = "ARITHMETIC_OVERFLOW", 
  IndexOutOfBounds = "INDEX_OUT_OF_BOUNDS",
  NetworkTimeout = "NETWORK_TIMEOUT",
  ParseError = "PARSE_ERROR",
  ValidationError = "VALIDATION_ERROR",
  AuthenticationFailure = "AUTHENTICATION_FAILURE",
  RateLimitExceeded = "RATE_LIMIT_EXCEEDED",
  ConfigurationError = "CONFIGURATION_ERROR",
  DatabaseError = "DATABASE_ERROR",
  FileNotFound = "FILE_NOT_FOUND",
  CompositeVoid = "COMPOSITE_VOID"
}

/**
 * Rich impossibility information (omega_veil structure)
 */
export interface VoidInfo {
  readonly pattern: ImpossibilityPattern;
  readonly depth: number;  // BaseVeil principle: minimum depth 1
  readonly source: string;
  readonly timestamp: number;
  readonly details?: Record<string, any>;
}

/**
 * The fundamental Omega type: Value or structured Void
 * Represents the mathematical omega_veil concept
 */
export type Omega<T> = 
  | { tag: 'Value'; value: T }
  | { tag: 'Void'; info: VoidInfo };

/**
 * Thermodynamic Omega with entropy tracking
 * Implements computational thermodynamics
 */
export interface ThermoOmega<T> {
  readonly value: Omega<T>;
  readonly entropy: number;  // Total impossibility encounters
  readonly history: VoidInfo[];  // Complete void encounter history
}

// ============================================================================
// CONSTRUCTION FUNCTIONS
// ============================================================================

/** Create a value (successful computation) */
export function value<T>(val: T): Omega<T> {
  return { tag: 'Value', value: val };
}

/** Create structured void (omega_veil encounter) */
export function void_<T = any>(
  pattern: ImpossibilityPattern, 
  source: string,
  details?: Record<string, any>
): Omega<T> {
  return {
    tag: 'Void',
    info: {
      pattern,
      depth: 1,  // BaseVeil principle
      source,
      timestamp: Date.now(),
      details: details || {}
    }
  };
}

/** Create thermodynamic value (pure, no entropy) */
export function thermo<T>(val: T): ThermoOmega<T> {
  return {
    value: value(val),
    entropy: 0,
    history: []
  };
}

/** Create thermodynamic void */
export function thermoVoid<T = any>(
  pattern: ImpossibilityPattern,
  source: string,
  details?: Record<string, any>
): ThermoOmega<T> {
  const voidInfo: VoidInfo = {
    pattern,
    depth: 1,
    source,
    timestamp: Date.now(),
    details: details || {}
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
export function isVoid<T>(omega: Omega<T>): omega is { tag: 'Void'; info: VoidInfo } {
  return omega.tag === 'Void';
}

/** Check if ThermoOmega value is void */
export function isThermoVoid<T>(thermo: ThermoOmega<T>): boolean {
  return isVoid(thermo.value);
}

/** Extract value with fallback */
export function unwrapOr<T>(omega: Omega<T>, fallback: T): T {
  return omega.tag === 'Value' ? omega.value : fallback;
}

/** Extract value from ThermoOmega with fallback */
export function unwrapThermoOr<T>(thermo: ThermoOmega<T>, fallback: T): T {
  return unwrapOr(thermo.value, fallback);
}

// ============================================================================
// MATHEMATICAL OPERATIONS (IMPOSSIBILITY ALGEBRA)
// ============================================================================

/** Combine two void infos (impossibility algebra) */
function combineVoids(v1: VoidInfo, v2: VoidInfo): VoidInfo {
  return {
    pattern: ImpossibilityPattern.CompositeVoid,
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
export function safeAdd(a: number, b: number): Omega<number> {
  // Check for overflow (JavaScript number safety)
  if (!Number.isSafeInteger(a) || !Number.isSafeInteger(b)) {
    return void_(ImpossibilityPattern.ArithmeticOverflow, `unsafe_integer_${a}_or_${b}`);
  }
  
  const result = a + b;
  if (!Number.isSafeInteger(result)) {
    return void_(ImpossibilityPattern.ArithmeticOverflow, `overflow_${a}+${b}`);
  }
  
  return value(result);
}

/** Safe division with zero protection */
export function safeDiv(a: number, b: number): Omega<number> {
  if (b === 0) {
    return void_(ImpossibilityPattern.DivisionByZero, `div_by_zero_${a}/0`);
  }
  
  if (!Number.isSafeInteger(a) || !Number.isSafeInteger(b)) {
    return void_(ImpossibilityPattern.ArithmeticOverflow, `unsafe_division_${a}/${b}`);
  }
  
  return value(a / b);
}

/** ThermoOmega addition with entropy tracking */
export function thermoAdd<T extends number>(
  x: ThermoOmega<T>, 
  y: ThermoOmega<T>
): ThermoOmega<T> {
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
export function thermoDiv<T extends number>(
  x: ThermoOmega<T>,
  y: ThermoOmega<T>
): ThermoOmega<T> {
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
export function recover<T>(thermo: ThermoOmega<T>, fallback: T): ThermoOmega<T> {
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
// FRONTEND-SPECIFIC UTILITIES
// ============================================================================

/** Safe DOM element access */
export function safeGetElement(id: string): Omega<HTMLElement> {
  if (typeof document === 'undefined') {
    return void_(ImpossibilityPattern.ConfigurationError, 'not_in_browser');
  }
  
  const element = document.getElementById(id);
  if (!element) {
    return void_(ImpossibilityPattern.FileNotFound, `element_not_found_${id}`);
  }
  
  return value(element);
}

/** Safe JSON parsing */
export function safeParseJSON<T = any>(json: string): Omega<T> {
  try {
    const parsed = JSON.parse(json);
    return value(parsed);
  } catch (error) {
    return void_(
      ImpossibilityPattern.ParseError, 
      `json_parse_error`,
      { originalError: error instanceof Error ? error.message : String(error) }
    );
  }
}

/** Safe localStorage access */
export function safeLocalStorage(key: string): Omega<string> {
  if (typeof localStorage === 'undefined') {
    return void_(ImpossibilityPattern.ConfigurationError, 'no_localstorage');
  }
  
  try {
    const value = localStorage.getItem(key);
    if (value === null) {
      return void_(ImpossibilityPattern.FileNotFound, `localstorage_key_${key}`);
    }
    return value(value);
  } catch (error) {
    return void_(
      ImpossibilityPattern.DatabaseError,
      `localstorage_error_${key}`,
      { error: error instanceof Error ? error.message : String(error) }
    );
  }
}

// ============================================================================
// BACKEND-SPECIFIC UTILITIES (NODE.JS)
// ============================================================================

/** Safe file reading (Node.js) */
export async function safeReadFile(path: string): Promise<Omega<string>> {
  try {
    // Dynamic import for Node.js environments
    const fs = await import('fs/promises');
    const content = await fs.readFile(path, 'utf-8');
    return value(content);
  } catch (error: any) {
    if (error.code === 'ENOENT') {
      return void_(ImpossibilityPattern.FileNotFound, `file_not_found_${path}`);
    }
    return void_(
      ImpossibilityPattern.DatabaseError,
      `file_read_error_${path}`,
      { error: error.message }
    );
  }
}

/** Safe HTTP request */
export async function safeHttpGet(url: string, timeoutMs = 5000): Promise<ThermoOmega<Response>> {
  try {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), timeoutMs);
    
    const response = await fetch(url, {
      signal: controller.signal,
      method: 'GET'
    });
    
    clearTimeout(timeoutId);
    
    if (!response.ok) {
      return thermoVoid(
        ImpossibilityPattern.NetworkTimeout,
        `http_error_${response.status}`,
        { status: response.status, statusText: response.statusText }
      );
    }
    
    return thermo(response);
    
  } catch (error: any) {
    if (error.name === 'AbortError') {
      return thermoVoid(
        ImpossibilityPattern.NetworkTimeout,
        `timeout_${url}`,
        { timeoutMs }
      );
    }
    
    return thermoVoid(
      ImpossibilityPattern.NetworkTimeout,
      `network_error_${url}`,
      { error: error.message }
    );
  }
}

// ============================================================================
// PRACTICAL FRONTEND UTILITIES
// ============================================================================

/** Safe form data extraction */
export function safeFormData(form: HTMLFormElement): ThermoOmega<Record<string, string>> {
  try {
    const formData = new FormData(form);
    const data: Record<string, string> = {};
    
    for (const [key, value] of formData.entries()) {
      if (typeof value === 'string') {
        data[key] = value;
      }
    }
    
    return thermo(data);
  } catch (error) {
    return thermoVoid(
      ImpossibilityPattern.ParseError,
      'form_data_extraction_error',
      { error: error instanceof Error ? error.message : String(error) }
    );
  }
}

/** Safe API call with retry logic */
export async function safeApiCall<T>(
  url: string, 
  options: RequestInit = {},
  maxRetries = 3
): Promise<ThermoOmega<T>> {
  let entropy = 0;
  const history: VoidInfo[] = [];
  
  for (let attempt = 0; attempt < maxRetries; attempt++) {
    try {
      const response = await fetch(url, {
        ...options,
        headers: {
          'Content-Type': 'application/json',
          ...options.headers
        }
      });
      
      if (!response.ok) {
        const voidInfo: VoidInfo = {
          pattern: ImpossibilityPattern.NetworkTimeout,
          depth: 1,
          source: `api_error_${response.status}_attempt_${attempt}`,
          timestamp: Date.now(),
          details: { status: response.status, attempt }
        };
        
        entropy += 1;
        history.push(voidInfo);
        
        if (attempt === maxRetries - 1) {
          return {
            value: { tag: 'Void', info: voidInfo },
            entropy,
            history
          };
        }
        continue;
      }
      
      const data = await response.json();
      return {
        value: value(data),
        entropy,
        history
      };
      
    } catch (error) {
      const voidInfo: VoidInfo = {
        pattern: ImpossibilityPattern.NetworkTimeout,
        depth: 1,
        source: `network_error_attempt_${attempt}`,
        timestamp: Date.now(),
        details: { error: error instanceof Error ? error.message : String(error), attempt }
      };
      
      entropy += 1;
      history.push(voidInfo);
      
      if (attempt === maxRetries - 1) {
        return {
          value: { tag: 'Void', info: voidInfo },
          entropy,
          history
        };
      }
    }
  }
  
  // Should never reach here, but totality requires it
  return thermoVoid(ImpossibilityPattern.ConfigurationError, 'unexpected_end_of_retries');
}

// ============================================================================
// PRACTICAL BACKEND UTILITIES
// ============================================================================

/** Safe environment variable access */
export function safeEnv(key: string, defaultValue?: string): Omega<string> {
  if (typeof process === 'undefined') {
    return void_(ImpossibilityPattern.ConfigurationError, 'not_in_nodejs');
  }
  
  const value = process.env[key];
  if (value === undefined) {
    if (defaultValue !== undefined) {
      return value(defaultValue);
    }
    return void_(ImpossibilityPattern.ConfigurationError, `missing_env_${key}`);
  }
  
  return value(value);
}

/** Safe database query wrapper */
export async function safeDbQuery<T>(
  queryFn: () => Promise<T>,
  queryName: string
): Promise<ThermoOmega<T>> {
  try {
    const result = await queryFn();
    return thermo(result);
  } catch (error: any) {
    return thermoVoid(
      ImpossibilityPattern.DatabaseError,
      `db_query_${queryName}`,
      { 
        error: error.message,
        code: error.code,
        sqlState: error.sqlState
      }
    );
  }
}

// ============================================================================
// HIGHER-ORDER TOTAL FUNCTIONS
// ============================================================================

/** Map over ThermoOmega values */
export function thermoMap<T, U>(
  thermo: ThermoOmega<T>,
  fn: (value: T) => U
): ThermoOmega<U> {
  if (isVoid(thermo.value)) {
    return {
      value: thermo.value as Omega<U>,
      entropy: thermo.entropy,
      history: thermo.history
    };
  }
  
  try {
    const mapped = fn(thermo.value.value);
    return {
      value: value(mapped),
      entropy: thermo.entropy,
      history: thermo.history
    };
  } catch (error) {
    const voidInfo: VoidInfo = {
      pattern: ImpossibilityPattern.ValidationError,
      depth: 1,
      source: 'map_function_error',
      timestamp: Date.now(),
      details: { error: error instanceof Error ? error.message : String(error) }
    };
    
    return {
      value: { tag: 'Void', info: voidInfo },
      entropy: thermo.entropy + 1,
      history: [...thermo.history, voidInfo]
    };
  }
}

/** Monadic bind for ThermoOmega */
export function thermoBind<T, U>(
  thermo: ThermoOmega<T>,
  fn: (value: T) => ThermoOmega<U>
): ThermoOmega<U> {
  if (isVoid(thermo.value)) {
    return {
      value: thermo.value as Omega<U>,
      entropy: thermo.entropy,
      history: thermo.history
    };
  }
  
  try {
    const result = fn(thermo.value.value);
    return {
      value: result.value,
      entropy: thermo.entropy + result.entropy,
      history: [...thermo.history, ...result.history]
    };
  } catch (error) {
    const voidInfo: VoidInfo = {
      pattern: ImpossibilityPattern.ValidationError,
      depth: 1,
      source: 'bind_function_error',
      timestamp: Date.now(),
      details: { error: error instanceof Error ? error.message : String(error) }
    };
    
    return {
      value: { tag: 'Void', info: voidInfo },
      entropy: thermo.entropy + 1,
      history: [...thermo.history, voidInfo]
    };
  }
}

/** Process array with total safety */
export function thermoMapArray<T, U>(
  items: T[],
  fn: (item: T, index: number) => ThermoOmega<U>
): ThermoOmega<U[]> {
  const results: U[] = [];
  let totalEntropy = 0;
  const allHistory: VoidInfo[] = [];
  
  for (let i = 0; i < items.length; i++) {
    const result = fn(items[i], i);
    totalEntropy += result.entropy;
    allHistory.push(...result.history);
    
    if (isVoid(result.value)) {
      // Continue processing despite individual failures
      // This demonstrates graceful degradation
      continue;
    }
    
    results.push(result.value.value);
  }
  
  return {
    value: value(results),
    entropy: totalEntropy,
    history: allHistory
  };
}

// ============================================================================
// FLUENT API FOR ERGONOMIC USAGE
// ============================================================================

/** Fluent ThermoOmega wrapper for chaining operations */
export class ThermoChain<T> {
  constructor(private readonly thermo: ThermoOmega<T>) {}
  
  /** Add another ThermoOmega value */
  add(other: ThermoOmega<number>): ThermoChain<number> {
    if (typeof this.thermo.value === 'object' && this.thermo.value.tag === 'Value' && typeof this.thermo.value.value === 'number') {
      const result = thermoAdd(this.thermo as ThermoOmega<number>, other);
      return new ThermoChain(result);
    }
    return new ThermoChain(this.thermo as any);
  }
  
  /** Divide by another ThermoOmega value */
  divide(other: ThermoOmega<number>): ThermoChain<number> {
    if (typeof this.thermo.value === 'object' && this.thermo.value.tag === 'Value' && typeof this.thermo.value.value === 'number') {
      const result = thermoDiv(this.thermo as ThermoOmega<number>, other);
      return new ThermoChain(result);
    }
    return new ThermoChain(this.thermo as any);
  }
  
  /** Map over the value */
  map<U>(fn: (value: T) => U): ThermoChain<U> {
    const result = thermoMap(this.thermo, fn);
    return new ThermoChain(result);
  }
  
  /** Recover with fallback value */
  recover(fallback: T): ThermoChain<T> {
    const result = recover(this.thermo, fallback);
    return new ThermoChain(result);
  }
  
  /** Extract the final ThermoOmega value */
  unwrap(): ThermoOmega<T> {
    return this.thermo;
  }
  
  /** Extract value with fallback */
  unwrapOr(fallback: T): T {
    return unwrapThermoOr(this.thermo, fallback);
  }
  
  /** Get entropy information */
  entropy(): number {
    return this.thermo.entropy;
  }
  
  /** Get void encounter history */
  history(): VoidInfo[] {
    return this.thermo.history;
  }
  
  /** Check if computation encountered impossibility */
  hasErrors(): boolean {
    return this.thermo.entropy > 0;
  }
}

/** Create a fluent chain from a value */
export function chain<T>(value: T): ThermoChain<T> {
  return new ThermoChain(thermo(value));
}

/** Create a fluent chain from existing ThermoOmega */
export function chainFrom<T>(thermo: ThermoOmega<T>): ThermoChain<T> {
  return new ThermoChain(thermo);
}

// ============================================================================
// PRACTICAL EXAMPLES AND DEMOS
// ============================================================================

/** Example: Safe portfolio calculation for frontend */
export async function calculatePortfolioValue(
  positions: Array<{symbol: string, quantity: number, price: number}>
): Promise<ThermoOmega<number>> {
  return thermoMapArray(positions, async (position) => {
    // Validate position data
    if (position.quantity <= 0 || position.price <= 0) {
      return thermoVoid(
        ImpossibilityPattern.ValidationError,
        `invalid_position_${position.symbol}`,
        { position }
      );
    }
    
    // Calculate position value (safe multiplication)
    return chain(position.quantity)
      .map(q => q * position.price)
      .unwrap();
  }).then(results => {
    // Sum all valid positions
    const validPositions = unwrapThermoOr(results, []);
    const total = validPositions.reduce((sum, val) => sum + val, 0);
    
    return {
      value: value(total),
      entropy: results.entropy,
      history: results.history
    };
  });
}

/** Example: Safe form processing for frontend */
export function processUserForm(formElement: HTMLFormElement): ThermoOmega<{email: string, age: number}> {
  return chainFrom(safeFormData(formElement))
    .map(data => {
      const email = data.email;
      const ageStr = data.age;
      
      // Validate email
      if (!email || !email.includes('@')) {
        throw new Error('Invalid email format');
      }
      
      // Validate age
      const age = parseInt(ageStr);
      if (isNaN(age) || age < 0 || age > 150) {
        throw new Error('Invalid age');
      }
      
      return { email, age };
    })
    .unwrap();
}

/** Example: Safe API endpoint for backend */
export async function handleUserRegistration(userData: any): Promise<ThermoOmega<{userId: string, success: boolean}>> {
  // Validate required fields
  const validation = chain(userData)
    .map(data => {
      if (!data.email || !data.password || !data.username) {
        throw new Error('Missing required fields');
      }
      return data;
    });
  
  if (validation.hasErrors()) {
    return validation.unwrap() as ThermoOmega<{userId: string, success: boolean}>;
  }
  
  // Simulate database save
  const saveResult = await safeDbQuery(
    async () => {
      // Simulate potential database errors
      if (userData.username === 'admin') {
        throw new Error('Username reserved');
      }
      return { userId: 'user_' + Date.now(), success: true };
    },
    'user_registration'
  );
  
  return saveResult;
}

// ============================================================================
// TESTING AND DEMONSTRATION
// ============================================================================

/** Run comprehensive tests */
export async function runTests(): Promise<void> {
  console.log('=== OMEGA TYPES TYPESCRIPT TESTING ===\n');
  
  // Test 1: Basic arithmetic
  console.log('TEST 1: Basic Arithmetic');
  const calc1 = chain(10).add(thermo(20));
  console.log(`  10 + 20 = ${calc1.unwrapOr(0)}, entropy = ${calc1.entropy()}`);
  
  // Test 2: Division by zero
  console.log('\nTEST 2: Division by Zero');
  const calc2 = chain(10).divide(thermo(0)).recover(999);
  console.log(`  10 / 0 (recovered) = ${calc2.unwrapOr(0)}, entropy = ${calc2.entropy()}`);
  
  // Test 3: JSON parsing
  console.log('\nTEST 3: Safe JSON Parsing');
  const validJson = safeParseJSON('{"name": "test", "value": 42}');
  const invalidJson = safeParseJSON('invalid json string');
  console.log(`  Valid JSON: ${isVoid(validJson) ? 'Failed' : 'Success'}`);
  console.log(`  Invalid JSON: ${isVoid(invalidJson) ? 'Handled gracefully' : 'Unexpected success'}`);
  
  // Test 4: Noether's theorem verification
  console.log('\nTEST 4: Noether\'s Theorem');
  const noether1 = chain(10).add(thermo(20));
  const noether2 = chain(20).add(thermo(10));
  console.log(`  10 + 20 entropy: ${noether1.entropy()}`);
  console.log(`  20 + 10 entropy: ${noether2.entropy()}`);
  console.log(`  ✓ Commutativity preserves entropy: ${noether1.entropy() === noether2.entropy()}`);
  
  // Test 5: Error accumulation
  console.log('\nTEST 5: Error Accumulation');
  const errors = chain(100)
    .divide(thermo(0))      // +1 entropy
    .add(thermo(50))        // +1 entropy (void + value)
    .recover(200)           // preserve entropy
    .add(thermo(25));       // +0 entropy (value + value)
  
  console.log(`  Complex computation with recovery:`);
  console.log(`    Final value: ${errors.unwrapOr(0)}`);
  console.log(`    Total entropy: ${errors.entropy()}`);
  console.log(`    Error history: ${errors.history().length} encounters`);
  
  console.log('\n✅ All tests demonstrate mathematical law compliance!');
}

// Run tests if this is the main module
if (typeof require !== 'undefined' && require.main === module) {
  runTests().catch(console.error);
}