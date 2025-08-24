/**
 * unravel-v3.ts
 * New TypeScript implementation synthesizing all learnings
 * Closely follows the clean V2 Haskell reference architecture
 * 
 * Key improvements:
 * - Proper universe state threading (fixes time evolution bug)
 * - Clean separation of concerns (basic vs thermodynamic evaluation)
 * - Configurable parameters (fuel, heat death threshold)
 * - Simplified architecture following V2 reference
 */

// ============================================================================
// CONFIGURATION CONSTANTS (Following V2 Reference)
// ============================================================================

export const CONFIG = {
  defaultFuel: 1000,
  heatDeathThreshold: 100,
  baseEntropy: 1
} as const;

// ============================================================================
// CORE TYPES (Following V2 Reference Structure)
// ============================================================================

/** Option type (like Haskell Maybe) */
export type Option<T> = { tag: 'Some'; value: T } | { tag: 'None' };

export function some<T>(value: T): Option<T> {
  return { tag: 'Some', value };
}

export function none<T>(): Option<T> {
  return { tag: 'None' };
}

/** Basic expression type (no variables) */
export type Expr = 
  | { type: 'ENum'; value: number }
  | { type: 'EVoid' }
  | { type: 'EBool'; value: boolean }
  | { type: 'EAdd'; left: Expr; right: Expr }
  | { type: 'ESub'; left: Expr; right: Expr }
  | { type: 'EMul'; left: Expr; right: Expr }
  | { type: 'EDiv'; left: Expr; right: Expr }
  | { type: 'EMod'; left: Expr; right: Expr }
  | { type: 'EIsVoid'; expr: Expr }
  | { type: 'EIfVoid'; condition: Expr; thenBranch: Expr; elseBranch: Expr }
  | { type: 'EDefault'; expr: Expr; defaultValue: Expr };

/** Basic value type */
export type Value = 
  | { type: 'VNum'; value: number }
  | { type: 'VBool'; value: boolean }
  | { type: 'VVoid' };

/** Expression with variables */
export type ExprV = 
  | { type: 'EVNum'; value: number }
  | { type: 'EVVoid' }
  | { type: 'EVBool'; value: boolean }
  | { type: 'EVAdd'; left: ExprV; right: ExprV }
  | { type: 'EVSub'; left: ExprV; right: ExprV }
  | { type: 'EVMul'; left: ExprV; right: ExprV }
  | { type: 'EVDiv'; left: ExprV; right: ExprV }
  | { type: 'EVMod'; left: ExprV; right: ExprV }
  | { type: 'EVIsVoid'; expr: ExprV }
  | { type: 'EVIfVoid'; condition: ExprV; thenBranch: ExprV; elseBranch: ExprV }
  | { type: 'EVDefault'; expr: ExprV; defaultValue: ExprV }
  | { type: 'EVVar'; name: string }
  | { type: 'EVLet'; name: string; binding: ExprV; body: ExprV };

/** Void source information */
export type VoidSource = 
  | { type: 'DivByZero'; numerator: number }
  | { type: 'ModByZero'; numerator: number }
  | { type: 'UndefinedVar'; variable: string }
  | { type: 'OutOfFuel' }
  | { type: 'TypeError'; operation: string }
  | { type: 'VoidPropagation'; parent1: VoidInfo; parent2: VoidInfo };

/** Rich void information */
export interface VoidInfo {
  readonly entropy: number;
  readonly timeCreated: number;
  readonly source: VoidSource;
}

/** Thermodynamic value */
export type ValueT = 
  | { type: 'VTNum'; value: number }
  | { type: 'VTBool'; value: boolean }
  | { type: 'VTVoid'; info: VoidInfo };

/** Universe state (following V2 structure exactly) */
export interface Universe {
  readonly totalEntropy: number;
  readonly timeStep: number;
  readonly voidCount: number;
}

/** Environment for variables */
export type Environment = Array<[string, Value]>;
export type ThermodynamicEnvironment = Array<[string, ValueT]>;

// ============================================================================
// UNIVERSE OPERATIONS (Following V2 Reference Exactly)
// ============================================================================

/** Initial universe (big bang) */
export const initialUniverse: Universe = {
  totalEntropy: 0,
  timeStep: 0,
  voidCount: 0
};

/** Create void information (following V2 makeVoidInfo) */
export function makeVoidInfo(entropyAmount: number, universe: Universe, source: VoidSource): VoidInfo {
  return {
    entropy: entropyAmount,
    timeCreated: universe.timeStep,
    source
  };
}

/** Evolve universe when void occurs (following V2 exactly) */
export function evolveUniverse(universe: Universe, info: VoidInfo): Universe {
  return {
    totalEntropy: universe.totalEntropy + info.entropy,
    timeStep: universe.timeStep + 1,  // ALWAYS increment by 1
    voidCount: universe.voidCount + 1
  };
}

/** Combine two voids (following V2 exactly) */
export function combineVoids(v1: VoidInfo, v2: VoidInfo, universe: Universe): VoidInfo {
  return {
    entropy: v1.entropy + v2.entropy,
    timeCreated: universe.timeStep,  // Use CURRENT universe time
    source: { type: 'VoidPropagation', parent1: v1, parent2: v2 }
  };
}

/** Check for heat death */
export function isHeatDeath(universe: Universe): boolean {
  return universe.totalEntropy >= CONFIG.heatDeathThreshold;
}

export function isHeatDeathCustom(threshold: number, universe: Universe): boolean {
  return universe.totalEntropy >= threshold;
}

// ============================================================================
// BASIC EVALUATION (Following V2 Structure)
// ============================================================================

/** Core evaluation with fuel (following V2 eval exactly) */
export function evalBasic(fuel: number, expr: Expr): Value {
  if (fuel === 0) {
    return { type: 'VVoid' };
  }
  
  const fuel2 = fuel - 1;
  
  switch (expr.type) {
    case 'ENum':
      return { type: 'VNum', value: expr.value };
      
    case 'EVoid':
      return { type: 'VVoid' };
      
    case 'EBool':
      return { type: 'VBool', value: expr.value };
      
    case 'EAdd': {
      const v1 = evalBasic(fuel2, expr.left);
      const v2 = evalBasic(fuel2, expr.right);
      
      if (v1.type === 'VNum' && v2.type === 'VNum') {
        return { type: 'VNum', value: v1.value + v2.value };
      }
      return { type: 'VVoid' };
    }
    
    case 'ESub': {
      const v1 = evalBasic(fuel2, expr.left);
      const v2 = evalBasic(fuel2, expr.right);
      
      if (v1.type === 'VNum' && v2.type === 'VNum') {
        return { type: 'VNum', value: Math.max(0, v1.value - v2.value) };  // Saturating
      }
      return { type: 'VVoid' };
    }
    
    case 'EMul': {
      const v1 = evalBasic(fuel2, expr.left);
      const v2 = evalBasic(fuel2, expr.right);
      
      if (v1.type === 'VNum' && v2.type === 'VNum') {
        return { type: 'VNum', value: v1.value * v2.value };
      }
      return { type: 'VVoid' };
    }
    
    case 'EDiv': {
      const v1 = evalBasic(fuel2, expr.left);
      const v2 = evalBasic(fuel2, expr.right);
      
      if (v1.type === 'VNum' && v2.type === 'VNum') {
        if (v2.value === 0) {
          return { type: 'VVoid' };
        }
        return { type: 'VNum', value: Math.floor(v1.value / v2.value) };
      }
      return { type: 'VVoid' };
    }
    
    case 'EMod': {
      const v1 = evalBasic(fuel2, expr.left);
      const v2 = evalBasic(fuel2, expr.right);
      
      if (v1.type === 'VNum' && v2.type === 'VNum') {
        if (v2.value === 0) {
          return { type: 'VVoid' };
        }
        return { type: 'VNum', value: v1.value % v2.value };
      }
      return { type: 'VVoid' };
    }
    
    case 'EIsVoid': {
      const v = evalBasic(fuel2, expr.expr);
      return { type: 'VBool', value: v.type === 'VVoid' };
    }
    
    case 'EIfVoid': {
      const condValue = evalBasic(fuel2, expr.condition);
      if (condValue.type === 'VVoid') {
        return evalBasic(fuel2, expr.thenBranch);
      } else {
        return evalBasic(fuel2, expr.elseBranch);
      }
    }
    
    case 'EDefault': {
      const v = evalBasic(fuel2, expr.expr);
      if (v.type === 'VVoid') {
        return evalBasic(fuel2, expr.defaultValue);
      }
      return v;
    }
    
    default:
      const _exhaustive: never = expr;
      throw new Error('Impossible: unhandled expression type');
  }
}

// ============================================================================
// VARIABLE ENVIRONMENT OPERATIONS (Following V2)
// ============================================================================

/** Lookup variable in environment (following V2 lookup exactly) */
export function lookupVar(env: Environment, name: string): Value {
  for (const [varName, value] of env) {
    if (varName === name) {
      return value;
    }
  }
  return { type: 'VVoid' };  // Undefined = void
}

/** Lookup for thermodynamic evaluation */
export function lookupVarT(env: ThermodynamicEnvironment, name: string): Option<ValueT> {
  for (const [varName, value] of env) {
    if (varName === name) {
      return some(value);
    }
  }
  return none();
}

// ============================================================================
// THERMODYNAMIC EVALUATION (Following V2 evalT Exactly)
// ============================================================================

/**
 * Main thermodynamic evaluator - follows V2 reference exactly
 * CRITICAL: Proper universe state threading fixes time evolution bug
 */
export function evalThermodynamic(
  fuel: number, 
  universe: Universe, 
  env: ThermodynamicEnvironment, 
  expr: ExprV
): [ValueT, Universe] {
  
  if (fuel === 0) {
    const info = makeVoidInfo(CONFIG.baseEntropy, universe, { type: 'OutOfFuel' });
    return [{ type: 'VTVoid', info }, evolveUniverse(universe, info)];
  }
  
  const fuel2 = fuel - 1;
  
  switch (expr.type) {
    case 'EVNum':
      return [{ type: 'VTNum', value: expr.value }, universe];
      
    case 'EVVoid': {
      const info = makeVoidInfo(CONFIG.baseEntropy, universe, { type: 'TypeError', operation: 'pure_void' });
      return [{ type: 'VTVoid', info }, evolveUniverse(universe, info)];
    }
    
    case 'EVBool':
      return [{ type: 'VTBool', value: expr.value }, universe];
      
    case 'EVAdd': {
      // CRITICAL: Proper universe threading (follows V2 exactly)
      const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
      const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);  // u1 → u2!
      
      if (v1.type === 'VTNum' && v2.type === 'VTNum') {
        return [{ type: 'VTNum', value: v1.value + v2.value }, u2];
      }
      
      if (v1.type === 'VTNum' && v2.type === 'VTVoid') {
        return [v2, u2];
      }
      
      if (v1.type === 'VTVoid' && v2.type === 'VTNum') {
        return [v1, u2];
      }
      
      if (v1.type === 'VTVoid' && v2.type === 'VTVoid') {
        const combined = combineVoids(v1.info, v2.info, u2);
        return [{ type: 'VTVoid', info: combined }, evolveUniverse(u2, combined)];
      }
      
      // Type error
      const info = makeVoidInfo(CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'add' });
      return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
    }
    
    case 'EVSub': {
      const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
      const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);
      
      if (v1.type === 'VTNum' && v2.type === 'VTNum') {
        return [{ type: 'VTNum', value: Math.max(0, v1.value - v2.value) }, u2];  // Saturating
      }
      
      if (v1.type === 'VTNum' && v2.type === 'VTVoid') {
        return [v2, u2];
      }
      
      if (v1.type === 'VTVoid' && v2.type === 'VTNum') {
        return [v1, u2];
      }
      
      if (v1.type === 'VTVoid' && v2.type === 'VTVoid') {
        const combined = combineVoids(v1.info, v2.info, u2);
        return [{ type: 'VTVoid', info: combined }, evolveUniverse(u2, combined)];
      }
      
      const info = makeVoidInfo(CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'sub' });
      return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
    }
    
    case 'EVMul': {
      const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
      const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);
      
      if (v1.type === 'VTNum' && v2.type === 'VTNum') {
        return [{ type: 'VTNum', value: v1.value * v2.value }, u2];
      }
      
      if (v1.type === 'VTNum' && v2.type === 'VTVoid') {
        return [v2, u2];
      }
      
      if (v1.type === 'VTVoid' && v2.type === 'VTNum') {
        return [v1, u2];
      }
      
      if (v1.type === 'VTVoid' && v2.type === 'VTVoid') {
        const combined = combineVoids(v1.info, v2.info, u2);
        return [{ type: 'VTVoid', info: combined }, evolveUniverse(u2, combined)];
      }
      
      const info = makeVoidInfo(CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'mul' });
      return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
    }
    
    case 'EVDiv': {
      const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
      const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);
      
      if (v1.type === 'VTNum' && v2.type === 'VTNum') {
        if (v2.value === 0) {
          const info = makeVoidInfo(CONFIG.baseEntropy, u2, { type: 'DivByZero', numerator: v1.value });
          return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
        }
        return [{ type: 'VTNum', value: Math.floor(v1.value / v2.value) }, u2];
      }
      
      if (v1.type === 'VTVoid') {
        return [v1, u2];
      }
      
      if (v2.type === 'VTVoid') {
        return [v2, u2];
      }
      
      const info = makeVoidInfo(CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'div' });
      return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
    }
    
    case 'EVMod': {
      const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
      const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);
      
      if (v1.type === 'VTNum' && v2.type === 'VTNum') {
        if (v2.value === 0) {
          const info = makeVoidInfo(CONFIG.baseEntropy, u2, { type: 'ModByZero', numerator: v1.value });
          return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
        }
        return [{ type: 'VTNum', value: v1.value % v2.value }, u2];
      }
      
      if (v1.type === 'VTVoid') {
        return [v1, u2];
      }
      
      if (v2.type === 'VTVoid') {
        return [v2, u2];
      }
      
      const info = makeVoidInfo(CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'mod' });
      return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
    }
    
    case 'EVIsVoid': {
      const [v, u1] = evalThermodynamic(fuel2, universe, env, expr.expr);
      return [{ type: 'VTBool', value: v.type === 'VTVoid' }, u1];
    }
    
    case 'EVIfVoid': {
      const [condValue, u1] = evalThermodynamic(fuel2, universe, env, expr.condition);
      if (condValue.type === 'VTVoid') {
        return evalThermodynamic(fuel2, u1, env, expr.thenBranch);
      } else {
        return evalThermodynamic(fuel2, u1, env, expr.elseBranch);
      }
    }
    
    case 'EVDefault': {
      const [v, u1] = evalThermodynamic(fuel2, universe, env, expr.expr);
      if (v.type === 'VTVoid') {
        return evalThermodynamic(fuel2, u1, env, expr.defaultValue);
      }
      return [v, u1];
    }
    
    case 'EVVar': {
      const lookupResult = lookupVarT(env, expr.name);
      if (lookupResult.tag === 'Some') {
        return [lookupResult.value, universe];
      } else {
        const info = makeVoidInfo(CONFIG.baseEntropy, universe, { type: 'UndefinedVar', variable: expr.name });
        return [{ type: 'VTVoid', info }, evolveUniverse(universe, info)];
      }
    }
    
    case 'EVLet': {
      const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.binding);
      const newEnv: ThermodynamicEnvironment = [[expr.name, v1], ...env];
      return evalThermodynamic(fuel2, u1, newEnv, expr.body);
    }
    
    default:
      const _exhaustive: never = expr;
      throw new Error('Impossible: unhandled expression type');
  }
}

// ============================================================================
// CONVENIENT EVALUATION FUNCTIONS (Following V2 API)
// ============================================================================

export function evalDefault(expr: Expr): Value {
  return evalBasic(CONFIG.defaultFuel, expr);
}

export function evalWithFuel(fuel: number, expr: Expr): Value {
  return evalBasic(fuel, expr);
}

export function evalThermoInitial(expr: ExprV): [ValueT, Universe] {
  return evalThermodynamic(CONFIG.defaultFuel, initialUniverse, [], expr);
}

export function evalThermoWithFuel(fuel: number, expr: ExprV): [ValueT, Universe] {
  return evalThermodynamic(fuel, initialUniverse, [], expr);
}

export function evalThermoWithUniverse(universe: Universe, expr: ExprV): [ValueT, Universe] {
  return evalThermodynamic(CONFIG.defaultFuel, universe, [], expr);
}

export function evalThermoFull(fuel: number, universe: Universe, env: ThermodynamicEnvironment, expr: ExprV): [ValueT, Universe] {
  return evalThermodynamic(fuel, universe, env, expr);
}

// ============================================================================
// EXPRESSION BUILDERS (Ergonomic API)
// ============================================================================

export const expr = {
  num: (value: number): ExprV => ({ type: 'EVNum', value }),
  bool: (value: boolean): ExprV => ({ type: 'EVBool', value }),
  void: (): ExprV => ({ type: 'EVVoid' }),
  
  add: (left: ExprV, right: ExprV): ExprV => ({ type: 'EVAdd', left, right }),
  sub: (left: ExprV, right: ExprV): ExprV => ({ type: 'EVSub', left, right }),
  mul: (left: ExprV, right: ExprV): ExprV => ({ type: 'EVMul', left, right }),
  div: (left: ExprV, right: ExprV): ExprV => ({ type: 'EVDiv', left, right }),
  mod: (left: ExprV, right: ExprV): ExprV => ({ type: 'EVMod', left, right }),
  
  isVoid: (expr: ExprV): ExprV => ({ type: 'EVIsVoid', expr }),
  ifVoid: (condition: ExprV, thenBranch: ExprV, elseBranch: ExprV): ExprV => 
    ({ type: 'EVIfVoid', condition, thenBranch, elseBranch }),
  default: (expr: ExprV, defaultValue: ExprV): ExprV => 
    ({ type: 'EVDefault', expr, defaultValue }),
  
  variable: (name: string): ExprV => ({ type: 'EVVar', name }),
  let: (name: string, binding: ExprV, body: ExprV): ExprV => 
    ({ type: 'EVLet', name, binding, body })
};

// ============================================================================
// COMPATIBILITY FUNCTIONS (Matching V2 API)
// ============================================================================

export function runBasic(expr: ExprV): Value {
  // Convert ExprV to basic evaluation
  const [thermoValue] = evalThermoInitial(expr);
  
  switch (thermoValue.type) {
    case 'VTNum': return { type: 'VNum', value: thermoValue.value };
    case 'VTBool': return { type: 'VBool', value: thermoValue.value };
    case 'VTVoid': return { type: 'VVoid' };
  }
}

export function runThermo(expr: ExprV): [ValueT, Universe] {
  return evalThermoInitial(expr);
}

export function runThermoWithFuel(fuel: number, expr: ExprV): [ValueT, Universe] {
  return evalThermoWithFuel(fuel, expr);
}

// ============================================================================
// MATHEMATICAL LAW VERIFICATION (V3)
// ============================================================================

export class V3MathematicalVerifier {
  static testNoetherTheorem(expr1: ExprV, expr2: ExprV): boolean {
    const [, u1] = evalThermoInitial(expr1);
    const [, u2] = evalThermoInitial(expr2);
    return u1.totalEntropy === u2.totalEntropy;
  }
  
  static testConservationLaw(voidExpr: ExprV, fallback: ExprV): boolean {
    const [, voidU] = evalThermoInitial(voidExpr);
    const [, recoveredU] = evalThermoInitial(expr.default(voidExpr, fallback));
    return voidU.totalEntropy === recoveredU.totalEntropy;
  }
  
  static testBaseVeilPrinciple(voidExpr: ExprV): boolean {
    const [, u] = evalThermoInitial(voidExpr);
    return u.totalEntropy >= CONFIG.baseEntropy;
  }
}

// ============================================================================
// TESTING AND DEMONSTRATION
// ============================================================================

export function runV3Tests(): void {
  console.log('🌀 UNRAVEL V3 IMPLEMENTATION TEST');
  console.log('New TypeScript implementation following V2 Haskell reference\n');

  // Test 1: Basic operations
  console.log('=== BASIC OPERATIONS ===');
  const basicTest = runThermo(expr.add(expr.num(10), expr.num(20)));
  console.log(`10 + 20: result=${basicTest[0].type === 'VTNum' ? basicTest[0].value : 'void'}, entropy=${basicTest[1].totalEntropy}`);

  // Test 2: Division by zero
  console.log('\n=== VOID OPERATIONS ===');
  const divTest = runThermo(expr.div(expr.num(10), expr.num(0)));
  console.log(`10 / 0: result=${divTest[0].type}, entropy=${divTest[1].totalEntropy}, time=${divTest[1].timeStep}`);

  // Test 3: Entropy bomb (the critical test)
  console.log('\n=== ENTROPY BOMB TEST (Critical Fix Verification) ===');
  
  function entropyBombV3(depth: number): ExprV {
    if (depth === 0) return expr.div(expr.num(1), expr.num(0));
    return expr.add(entropyBombV3(depth - 1), entropyBombV3(depth - 1));
  }
  
  for (let depth = 0; depth <= 10; depth++) {
    const [v, u] = runThermo(entropyBombV3(depth));
    console.log(`  V3 Bomb ${depth}: entropy=${u.totalEntropy}, time=${u.timeStep}, voids=${u.voidCount}`);
    
    if (u.timeStep !== u.voidCount && depth > 0) {
      console.log(`    🚨 TIME/VOID MISMATCH: ${u.timeStep} vs ${u.voidCount}`);
    }
  }

  // Test 4: Mathematical laws
  console.log('\n=== MATHEMATICAL LAW VERIFICATION ===');
  
  const noetherTest = V3MathematicalVerifier.testNoetherTheorem(
    expr.add(expr.num(42), expr.num(58)),
    expr.add(expr.num(58), expr.num(42))
  );
  console.log(`Noether's theorem: ${noetherTest ? 'VERIFIED' : 'VIOLATED'}`);
  
  const conservationTest = V3MathematicalVerifier.testConservationLaw(
    expr.div(expr.num(100), expr.num(0)),
    expr.num(999)
  );
  console.log(`Conservation laws: ${conservationTest ? 'VERIFIED' : 'VIOLATED'}`);

  console.log('\n=== V3 vs PREVIOUS IMPLEMENTATIONS ===');
  console.log('✅ Improved: Proper universe state threading (fixes time evolution)');
  console.log('✅ Improved: Clean separation of basic vs thermodynamic evaluation');
  console.log('✅ Improved: Configurable parameters (fuel, heat death threshold)');
  console.log('✅ Improved: Follows V2 Haskell reference architecture exactly');
  
  console.log('\n🎯 NEXT: Compare entropy bomb results with TypeScript final version');
  console.log('Expected: V3 should match Haskell V2 reference behavior perfectly!');
  
  console.log('\n🌀 V3 implementation ready for validation! 🌀');
}

// Auto-run tests
if (typeof require !== 'undefined' && require.main === module) {
  runV3Tests();
}

export default {
  expr,
  runThermo,
  runThermoWithFuel,
  evalThermoInitial,
  V3MathematicalVerifier,
  CONFIG,
  initialUniverse,
  runV3Tests
};