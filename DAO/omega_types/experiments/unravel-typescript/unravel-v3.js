"use strict";
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
Object.defineProperty(exports, "__esModule", { value: true });
exports.V3MathematicalVerifier = exports.expr = exports.initialUniverse = exports.CONFIG = void 0;
exports.some = some;
exports.none = none;
exports.makeVoidInfo = makeVoidInfo;
exports.evolveUniverse = evolveUniverse;
exports.combineVoids = combineVoids;
exports.isHeatDeath = isHeatDeath;
exports.isHeatDeathCustom = isHeatDeathCustom;
exports.evalBasic = evalBasic;
exports.lookupVar = lookupVar;
exports.lookupVarT = lookupVarT;
exports.evalThermodynamic = evalThermodynamic;
exports.evalDefault = evalDefault;
exports.evalWithFuel = evalWithFuel;
exports.evalThermoInitial = evalThermoInitial;
exports.evalThermoWithFuel = evalThermoWithFuel;
exports.evalThermoWithUniverse = evalThermoWithUniverse;
exports.evalThermoFull = evalThermoFull;
exports.runBasic = runBasic;
exports.runThermo = runThermo;
exports.runThermoWithFuel = runThermoWithFuel;
exports.runV3Tests = runV3Tests;
// ============================================================================
// CONFIGURATION CONSTANTS (Following V2 Reference)
// ============================================================================
exports.CONFIG = {
    defaultFuel: 1000,
    heatDeathThreshold: 100,
    baseEntropy: 1
};
function some(value) {
    return { tag: 'Some', value };
}
function none() {
    return { tag: 'None' };
}
// ============================================================================
// UNIVERSE OPERATIONS (Following V2 Reference Exactly)
// ============================================================================
/** Initial universe (big bang) */
exports.initialUniverse = {
    totalEntropy: 0,
    timeStep: 0,
    voidCount: 0
};
/** Create void information (following V2 makeVoidInfo) */
function makeVoidInfo(entropyAmount, universe, source) {
    return {
        entropy: entropyAmount,
        timeCreated: universe.timeStep,
        source
    };
}
/** Evolve universe when void occurs (following V2 exactly) */
function evolveUniverse(universe, info) {
    return {
        totalEntropy: universe.totalEntropy + info.entropy,
        timeStep: universe.timeStep + 1, // ALWAYS increment by 1
        voidCount: universe.voidCount + 1
    };
}
/** Combine two voids (following V2 exactly) */
function combineVoids(v1, v2, universe) {
    return {
        entropy: v1.entropy + v2.entropy,
        timeCreated: universe.timeStep, // Use CURRENT universe time
        source: { type: 'VoidPropagation', parent1: v1, parent2: v2 }
    };
}
/** Check for heat death */
function isHeatDeath(universe) {
    return universe.totalEntropy >= exports.CONFIG.heatDeathThreshold;
}
function isHeatDeathCustom(threshold, universe) {
    return universe.totalEntropy >= threshold;
}
// ============================================================================
// BASIC EVALUATION (Following V2 Structure)
// ============================================================================
/** Core evaluation with fuel (following V2 eval exactly) */
function evalBasic(fuel, expr) {
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
                return { type: 'VNum', value: Math.max(0, v1.value - v2.value) }; // Saturating
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
            }
            else {
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
            const _exhaustive = expr;
            throw new Error('Impossible: unhandled expression type');
    }
}
// ============================================================================
// VARIABLE ENVIRONMENT OPERATIONS (Following V2)
// ============================================================================
/** Lookup variable in environment (following V2 lookup exactly) */
function lookupVar(env, name) {
    for (const [varName, value] of env) {
        if (varName === name) {
            return value;
        }
    }
    return { type: 'VVoid' }; // Undefined = void
}
/** Lookup for thermodynamic evaluation */
function lookupVarT(env, name) {
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
function evalThermodynamic(fuel, universe, env, expr) {
    if (fuel === 0) {
        const info = makeVoidInfo(exports.CONFIG.baseEntropy, universe, { type: 'OutOfFuel' });
        return [{ type: 'VTVoid', info }, evolveUniverse(universe, info)];
    }
    const fuel2 = fuel - 1;
    switch (expr.type) {
        case 'EVNum':
            return [{ type: 'VTNum', value: expr.value }, universe];
        case 'EVVoid': {
            const info = makeVoidInfo(exports.CONFIG.baseEntropy, universe, { type: 'TypeError', operation: 'pure_void' });
            return [{ type: 'VTVoid', info }, evolveUniverse(universe, info)];
        }
        case 'EVBool':
            return [{ type: 'VTBool', value: expr.value }, universe];
        case 'EVAdd': {
            // CRITICAL: Proper universe threading (follows V2 exactly)
            const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
            const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right); // u1 → u2!
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
            const info = makeVoidInfo(exports.CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'add' });
            return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
        }
        case 'EVSub': {
            const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
            const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);
            if (v1.type === 'VTNum' && v2.type === 'VTNum') {
                return [{ type: 'VTNum', value: Math.max(0, v1.value - v2.value) }, u2]; // Saturating
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
            const info = makeVoidInfo(exports.CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'sub' });
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
            const info = makeVoidInfo(exports.CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'mul' });
            return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
        }
        case 'EVDiv': {
            const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
            const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);
            if (v1.type === 'VTNum' && v2.type === 'VTNum') {
                if (v2.value === 0) {
                    const info = makeVoidInfo(exports.CONFIG.baseEntropy, u2, { type: 'DivByZero', numerator: v1.value });
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
            const info = makeVoidInfo(exports.CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'div' });
            return [{ type: 'VTVoid', info }, evolveUniverse(u2, info)];
        }
        case 'EVMod': {
            const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.left);
            const [v2, u2] = evalThermodynamic(fuel2, u1, env, expr.right);
            if (v1.type === 'VTNum' && v2.type === 'VTNum') {
                if (v2.value === 0) {
                    const info = makeVoidInfo(exports.CONFIG.baseEntropy, u2, { type: 'ModByZero', numerator: v1.value });
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
            const info = makeVoidInfo(exports.CONFIG.baseEntropy, u2, { type: 'TypeError', operation: 'mod' });
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
            }
            else {
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
            }
            else {
                const info = makeVoidInfo(exports.CONFIG.baseEntropy, universe, { type: 'UndefinedVar', variable: expr.name });
                return [{ type: 'VTVoid', info }, evolveUniverse(universe, info)];
            }
        }
        case 'EVLet': {
            const [v1, u1] = evalThermodynamic(fuel2, universe, env, expr.binding);
            const newEnv = [[expr.name, v1], ...env];
            return evalThermodynamic(fuel2, u1, newEnv, expr.body);
        }
        default:
            const _exhaustive = expr;
            throw new Error('Impossible: unhandled expression type');
    }
}
// ============================================================================
// CONVENIENT EVALUATION FUNCTIONS (Following V2 API)
// ============================================================================
function evalDefault(expr) {
    return evalBasic(exports.CONFIG.defaultFuel, expr);
}
function evalWithFuel(fuel, expr) {
    return evalBasic(fuel, expr);
}
function evalThermoInitial(expr) {
    return evalThermodynamic(exports.CONFIG.defaultFuel, exports.initialUniverse, [], expr);
}
function evalThermoWithFuel(fuel, expr) {
    return evalThermodynamic(fuel, exports.initialUniverse, [], expr);
}
function evalThermoWithUniverse(universe, expr) {
    return evalThermodynamic(exports.CONFIG.defaultFuel, universe, [], expr);
}
function evalThermoFull(fuel, universe, env, expr) {
    return evalThermodynamic(fuel, universe, env, expr);
}
// ============================================================================
// EXPRESSION BUILDERS (Ergonomic API)
// ============================================================================
exports.expr = {
    num: (value) => ({ type: 'EVNum', value }),
    bool: (value) => ({ type: 'EVBool', value }),
    void: () => ({ type: 'EVVoid' }),
    add: (left, right) => ({ type: 'EVAdd', left, right }),
    sub: (left, right) => ({ type: 'EVSub', left, right }),
    mul: (left, right) => ({ type: 'EVMul', left, right }),
    div: (left, right) => ({ type: 'EVDiv', left, right }),
    mod: (left, right) => ({ type: 'EVMod', left, right }),
    isVoid: (expr) => ({ type: 'EVIsVoid', expr }),
    ifVoid: (condition, thenBranch, elseBranch) => ({ type: 'EVIfVoid', condition, thenBranch, elseBranch }),
    default: (expr, defaultValue) => ({ type: 'EVDefault', expr, defaultValue }),
    variable: (name) => ({ type: 'EVVar', name }),
    let: (name, binding, body) => ({ type: 'EVLet', name, binding, body })
};
// ============================================================================
// COMPATIBILITY FUNCTIONS (Matching V2 API)
// ============================================================================
function runBasic(expr) {
    // Convert ExprV to basic evaluation
    const [thermoValue] = evalThermoInitial(expr);
    switch (thermoValue.type) {
        case 'VTNum': return { type: 'VNum', value: thermoValue.value };
        case 'VTBool': return { type: 'VBool', value: thermoValue.value };
        case 'VTVoid': return { type: 'VVoid' };
    }
}
function runThermo(expr) {
    return evalThermoInitial(expr);
}
function runThermoWithFuel(fuel, expr) {
    return evalThermoWithFuel(fuel, expr);
}
// ============================================================================
// MATHEMATICAL LAW VERIFICATION (V3)
// ============================================================================
class V3MathematicalVerifier {
    static testNoetherTheorem(expr1, expr2) {
        const [, u1] = evalThermoInitial(expr1);
        const [, u2] = evalThermoInitial(expr2);
        return u1.totalEntropy === u2.totalEntropy;
    }
    static testConservationLaw(voidExpr, fallback) {
        const [, voidU] = evalThermoInitial(voidExpr);
        const [, recoveredU] = evalThermoInitial(exports.expr.default(voidExpr, fallback));
        return voidU.totalEntropy === recoveredU.totalEntropy;
    }
    static testBaseVeilPrinciple(voidExpr) {
        const [, u] = evalThermoInitial(voidExpr);
        return u.totalEntropy >= exports.CONFIG.baseEntropy;
    }
}
exports.V3MathematicalVerifier = V3MathematicalVerifier;
// ============================================================================
// TESTING AND DEMONSTRATION
// ============================================================================
function runV3Tests() {
    console.log('🌀 UNRAVEL V3 IMPLEMENTATION TEST');
    console.log('New TypeScript implementation following V2 Haskell reference\n');
    // Test 1: Basic operations
    console.log('=== BASIC OPERATIONS ===');
    const basicTest = runThermo(exports.expr.add(exports.expr.num(10), exports.expr.num(20)));
    console.log(`10 + 20: result=${basicTest[0].type === 'VTNum' ? basicTest[0].value : 'void'}, entropy=${basicTest[1].totalEntropy}`);
    // Test 2: Division by zero
    console.log('\n=== VOID OPERATIONS ===');
    const divTest = runThermo(exports.expr.div(exports.expr.num(10), exports.expr.num(0)));
    console.log(`10 / 0: result=${divTest[0].type}, entropy=${divTest[1].totalEntropy}, time=${divTest[1].timeStep}`);
    // Test 3: Entropy bomb (the critical test)
    console.log('\n=== ENTROPY BOMB TEST (Critical Fix Verification) ===');
    function entropyBombV3(depth) {
        if (depth === 0)
            return exports.expr.div(exports.expr.num(1), exports.expr.num(0));
        return exports.expr.add(entropyBombV3(depth - 1), entropyBombV3(depth - 1));
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
    const noetherTest = V3MathematicalVerifier.testNoetherTheorem(exports.expr.add(exports.expr.num(42), exports.expr.num(58)), exports.expr.add(exports.expr.num(58), exports.expr.num(42)));
    console.log(`Noether's theorem: ${noetherTest ? 'VERIFIED' : 'VIOLATED'}`);
    const conservationTest = V3MathematicalVerifier.testConservationLaw(exports.expr.div(exports.expr.num(100), exports.expr.num(0)), exports.expr.num(999));
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
exports.default = {
    expr: exports.expr,
    runThermo,
    runThermoWithFuel,
    evalThermoInitial,
    V3MathematicalVerifier,
    CONFIG: exports.CONFIG,
    initialUniverse: exports.initialUniverse,
    runV3Tests
};
