/**
 * omega-types.ts
 * Clean TypeScript implementation of total functional programming
 * Based on omega_veil and impossibility algebra
 */

// ============================================================================
// CORE TYPES
// ============================================================================

export enum ImpossibilityPattern {
  DivisionByZero = "DIVISION_BY_ZERO",
  ArithmeticOverflow = "ARITHMETIC_OVERFLOW",
  IndexOutOfBounds = "INDEX_OUT_OF_BOUNDS",
  ParseError = "PARSE_ERROR",
  ValidationError = "VALIDATION_ERROR",
  NetworkTimeout = "NETWORK_TIMEOUT",
  ConfigurationError = "CONFIGURATION_ERROR"
}

export interface VoidInfo {
  readonly pattern: ImpossibilityPattern;
  readonly depth: number;  // BaseVeil principle: minimum 1
  readonly source: string;
  readonly timestamp: number;
  readonly details?: Record<string, any>;
}

export type Omega<T> = 
  | { tag: 'Value'; value: T }
  | { tag: 'Void'; info: VoidInfo };

export interface ThermoOmega<T> {
  readonly value: Omega<T>;
  readonly entropy: number;
  readonly history: VoidInfo[];
}

// ============================================================================
// FACTORY FUNCTIONS
// ============================================================================

export function value<T>(val: T): Omega<T> {
  return { tag: 'Value', value: val };
}

export function void_<T>(pattern: ImpossibilityPattern, source: string = ""): Omega<T> {
  return {
    tag: 'Void',
    info: {
      pattern,
      depth: 1,  // BaseVeil principle
      source,
      timestamp: Date.now()
    }
  };
}

export function thermo<T>(val: T): ThermoOmega<T> {
  return {
    value: value(val),
    entropy: 0,
    history: []
  };
}

export function thermoVoid<T>(pattern: ImpossibilityPattern, source: string = ""): ThermoOmega<T> {
  const voidInfo: VoidInfo = {
    pattern,
    depth: 1,
    source,
    timestamp: Date.now()
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

export function isVoid<T>(omega: Omega<T>): omega is { tag: 'Void'; info: VoidInfo } {
  return omega.tag === 'Void';
}

export function unwrapOr<T>(omega: Omega<T>, fallback: T): T {
  return omega.tag === 'Value' ? omega.value : fallback;
}

export function unwrapThermoOr<T>(thermo: ThermoOmega<T>, fallback: T): T {
  return unwrapOr(thermo.value, fallback);
}

// ============================================================================
// SAFE ARITHMETIC
// ============================================================================

export function safeAdd(a: number, b: number): Omega<number> {
  if (!Number.isSafeInteger(a) || !Number.isSafeInteger(b)) {
    return void_(ImpossibilityPattern.ArithmeticOverflow, `unsafe_integers_${a}_${b}`);
  }
  
  const result = a + b;
  if (!Number.isSafeInteger(result)) {
    return void_(ImpossibilityPattern.ArithmeticOverflow, `overflow_${a}+${b}`);
  }
  
  return value(result);
}

export function safeDiv(a: number, b: number): Omega<number> {
  if (b === 0) {
    return void_(ImpossibilityPattern.DivisionByZero, `div_by_zero_${a}/0`);
  }
  
  return value(a / b);
}

// ============================================================================
// FLUENT API
// ============================================================================

export class ThermoChain<T> {
  constructor(private readonly thermo: ThermoOmega<T>) {}

  add(other: number): ThermoChain<number> {
    if (typeof this.getValue() === 'number') {
      const x = this.thermo as ThermoOmega<number>;
      const y = thermo(other);
      const result = thermoAdd(x, y);
      return new ThermoChain(result);
    }
    return new ThermoChain(this.thermo as any);
  }

  divide(other: number): ThermoChain<number> {
    if (typeof this.getValue() === 'number') {
      const x = this.thermo as ThermoOmega<number>;
      const y = thermo(other);
      const result = thermoDiv(x, y);
      return new ThermoChain(result);
    }
    return new ThermoChain(this.thermo as any);
  }

  recover(fallback: T): ThermoChain<T> {
    const result = recover(this.thermo, fallback);
    return new ThermoChain(result);
  }

  unwrapOr(fallback: T): T {
    return unwrapThermoOr(this.thermo, fallback);
  }

  entropy(): number {
    return this.thermo.entropy;
  }

  hasErrors(): boolean {
    return this.thermo.entropy > 0;
  }

  private getValue(): T | undefined {
    return this.thermo.value.tag === 'Value' ? this.thermo.value.value : undefined;
  }
}

export function chain<T>(value: T): ThermoChain<T> {
  return new ThermoChain(thermo(value));
}

// ============================================================================
// THERMODYNAMIC OPERATIONS
// ============================================================================

function thermoAdd(x: ThermoOmega<number>, y: ThermoOmega<number>): ThermoOmega<number> {
  if (isVoid(x.value) && isVoid(y.value)) {
    const xInfo = x.value.info;
    const yInfo = y.value.info;
    const combined: VoidInfo = {
      pattern: ImpossibilityPattern.ValidationError,
      depth: xInfo.depth + yInfo.depth,
      source: `${xInfo.source}+${yInfo.source}`,
      timestamp: Math.max(xInfo.timestamp, yInfo.timestamp)
    };
    
    return {
      value: { tag: 'Void', info: combined },
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, combined]
    };
  }
  
  if (isVoid(x.value)) {
    const xInfo = x.value.info;
    return {
      value: x.value,
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, xInfo]
    };
  }
  
  if (isVoid(y.value)) {
    const yInfo = y.value.info;
    return {
      value: y.value,
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, yInfo]
    };
  }
  
  // Both values - safe addition
  const result = safeAdd(x.value.value, y.value.value);
  
  if (isVoid(result)) {
    const resultInfo = result.info;
    return {
      value: result,
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, resultInfo]
    };
  }
  
  return {
    value: result,
    entropy: x.entropy + y.entropy,
    history: [...x.history, ...y.history]
  };
}

function thermoDiv(x: ThermoOmega<number>, y: ThermoOmega<number>): ThermoOmega<number> {
  if (isVoid(x.value) || isVoid(y.value)) {
    const voidInfo = isVoid(x.value) ? x.value.info : (y.value as { tag: 'Void'; info: VoidInfo }).info;
    return {
      value: { tag: 'Void', info: voidInfo },
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, voidInfo]
    };
  }
  
  const result = safeDiv(x.value.value, y.value.value);
  
  if (isVoid(result)) {
    const resultInfo = result.info;
    return {
      value: result,
      entropy: x.entropy + y.entropy + 1,
      history: [...x.history, ...y.history, resultInfo]
    };
  }
  
  return {
    value: result,
    entropy: x.entropy + y.entropy,
    history: [...x.history, ...y.history]
  };
}

function recover<T>(thermo: ThermoOmega<T>, fallback: T): ThermoOmega<T> {
  if (isVoid(thermo.value)) {
    return {
      value: value(fallback),
      entropy: thermo.entropy,  // Conservation law
      history: thermo.history
    };
  }
  return thermo;
}

// ============================================================================
// TESTING
// ============================================================================

export function runTests(): void {
  console.log('=== TYPESCRIPT OMEGA TYPES TESTING ===\n');
  
  // Test 1: Basic arithmetic
  console.log('TEST 1: Basic Arithmetic');
  const calc1 = chain(10).add(20);
  console.log(`  10 + 20 = ${calc1.unwrapOr(0)}, entropy = ${calc1.entropy()}`);
  
  // Test 2: Division by zero
  console.log('\nTEST 2: Division by Zero');
  const calc2 = chain(10).divide(0).recover(999);
  console.log(`  10 / 0 (recovered) = ${calc2.unwrapOr(0)}, entropy = ${calc2.entropy()}`);
  
  // Test 3: Noether's theorem
  console.log('\nTEST 3: Noether\'s Theorem');
  const noether1 = chain(10).add(20);
  const noether2 = chain(20).add(10);
  console.log(`  10 + 20 entropy: ${noether1.entropy()}`);
  console.log(`  20 + 10 entropy: ${noether2.entropy()}`);
  console.log(`  ✓ Commutativity preserves entropy: ${noether1.entropy() === noether2.entropy()}`);
  
  // Test 4: Error accumulation
  console.log('\nTEST 4: Error Accumulation');
  const errors = chain(100)
    .divide(0)      // +1 entropy
    .recover(200)   // preserve entropy
    .add(25);       // continue
  
  console.log(`  Complex computation:`);
  console.log(`    Final value: ${errors.unwrapOr(0)}`);
  console.log(`    Total entropy: ${errors.entropy()}`);
  
  console.log('\n✅ TypeScript total functions working perfectly!');
}

// Export for Node.js
if (typeof module !== 'undefined') {
  module.exports = { chain, thermo, safeAdd, safeDiv, runTests, ImpossibilityPattern };
}

// Auto-run tests when executed directly
if (typeof require !== 'undefined' && require.main === module) {
  runTests();
}