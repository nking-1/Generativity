"use strict";
/**
 * unravel-enhanced.ts
 * Enhanced TypeScript implementation matching the sophisticated Haskell original
 * Features rich void forensics, non-linear entropy, and complete failure genealogy
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.VoidForensics = exports.ev = exports.EnhancedUnravelEvaluator = exports.EnhancedEnvironment = exports.EnhancedUniverse = exports.VoidSourceType = void 0;
exports.runThermo = runThermo;
exports.evalDefault = evalDefault;
exports.runEnhancedDemo = runEnhancedDemo;
// ============================================================================
// ENHANCED THERMODYNAMIC SYSTEM (MATCHING HASKELL)
// ============================================================================
var VoidSourceType;
(function (VoidSourceType) {
    VoidSourceType["DivByZero"] = "DivByZero";
    VoidSourceType["ModByZero"] = "ModByZero";
    VoidSourceType["UndefinedVar"] = "UndefinedVar";
    VoidSourceType["OutOfFuel"] = "OutOfFuel";
    VoidSourceType["TypeError"] = "TypeError";
    VoidSourceType["VoidPropagation"] = "VoidPropagation";
})(VoidSourceType || (exports.VoidSourceType = VoidSourceType = {}));
/**
 * Enhanced computational universe with sophisticated entropy tracking
 */
class EnhancedUniverse {
    constructor() {
        this._totalEntropy = 0;
        this._timeStep = 0;
        this._voidCount = 0;
        this._forensicHistory = [];
    }
    get totalEntropy() { return this._totalEntropy; }
    get timeStep() { return this._timeStep; }
    get voidCount() { return this._voidCount; }
    get history() { return this._forensicHistory; }
    /**
     * Evolve universe when void is encountered
     * Implements evolve_universe from Coq specification
     */
    evolveUniverse(info) {
        this._totalEntropy += info.entropy; // Add entropy contribution
        this._timeStep++; // Advance computational time
        this._voidCount++; // Count void encounters
        this._forensicHistory.push(info); // Maintain complete history
    }
    /**
     * Combine two voids according to proven mathematical laws
     * Implements combine_voids with non-linear entropy growth
     */
    combineVoids(v1, v2) {
        return {
            entropy: v1.entropy + v2.entropy, // Entropies add
            timeStep: this._timeStep,
            source: {
                type: VoidSourceType.VoidPropagation,
                parent1: v1,
                parent2: v2
            }
        };
    }
    /**
     * Display universe state for debugging
     */
    toString() {
        return `Universe{entropy=${this._totalEntropy}, time=${this._timeStep}, voids=${this._voidCount}}`;
    }
    /**
     * Get health assessment
     */
    getHealthStatus() {
        if (this._totalEntropy === 0)
            return "Perfect";
        if (this._totalEntropy < 5)
            return "Good";
        if (this._totalEntropy < 15)
            return "Degraded";
        if (this._totalEntropy >= 50)
            return "Heat Death";
        return "Critical";
    }
}
exports.EnhancedUniverse = EnhancedUniverse;
// ============================================================================
// ENHANCED ENVIRONMENT WITH UNDEFINED = VOID
// ============================================================================
class EnhancedEnvironment {
    constructor() {
        this.bindings = new Map();
    }
    lookup(name, universe) {
        if (!this.bindings.has(name)) {
            const info = {
                entropy: 1,
                timeStep: universe.timeStep,
                source: { type: VoidSourceType.UndefinedVar, variable: name }
            };
            universe.evolveUniverse(info);
            return { type: 'VVoid', info };
        }
        return this.bindings.get(name);
    }
    bind(name, value) {
        const newEnv = new EnhancedEnvironment();
        newEnv.bindings = new Map(this.bindings);
        newEnv.bindings.set(name, value);
        return newEnv;
    }
}
exports.EnhancedEnvironment = EnhancedEnvironment;
// ============================================================================
// ENHANCED EVALUATOR (MATCHING HASKELL EVALV)
// ============================================================================
class EnhancedUnravelEvaluator {
    constructor(fuel, universe, env = new EnhancedEnvironment()) {
        this.fuel = fuel;
        this.universe = universe;
        this.env = env;
    }
    /**
     * Enhanced evaluation with rich void forensics
     */
    eval(expr) {
        // Fuel exhaustion = void
        if (this.fuel <= 0) {
            const info = {
                entropy: 1,
                timeStep: this.universe.timeStep,
                source: { type: VoidSourceType.OutOfFuel }
            };
            this.universe.evolveUniverse(info);
            return { type: 'VVoid', info };
        }
        this.fuel--;
        switch (expr.type) {
            case 'EVNum':
                return { type: 'VNum', value: expr.value };
            case 'EVBool':
                return { type: 'VBool', value: expr.value };
            case 'EVVoid':
                const explicitVoidInfo = {
                    entropy: 1,
                    timeStep: this.universe.timeStep,
                    source: { type: VoidSourceType.TypeError, operation: "explicit_void" }
                };
                this.universe.evolveUniverse(explicitVoidInfo);
                return { type: 'VVoid', info: explicitVoidInfo };
            case 'EVAdd':
            case 'EVSub':
            case 'EVMul':
                return this.evalArithmetic(expr.left, expr.right, expr.type.substring(2).toLowerCase(), (a, b) => {
                    switch (expr.type) {
                        case 'EVAdd': return a + b;
                        case 'EVSub': return Math.max(0, a - b); // Saturating subtraction
                        case 'EVMul': return a * b;
                        default: throw new Error('Impossible');
                    }
                });
            case 'EVDiv':
                return this.evalArithmetic(expr.left, expr.right, 'div', (a, b) => {
                    if (b === 0) {
                        const info = {
                            entropy: 1,
                            timeStep: this.universe.timeStep,
                            source: { type: VoidSourceType.DivByZero, numerator: a }
                        };
                        this.universe.evolveUniverse(info);
                        throw new VoidEncounterSignal(info);
                    }
                    return Math.floor(a / b);
                });
            case 'EVMod':
                return this.evalArithmetic(expr.left, expr.right, 'mod', (a, b) => {
                    if (b === 0) {
                        const info = {
                            entropy: 1,
                            timeStep: this.universe.timeStep,
                            source: { type: VoidSourceType.ModByZero, numerator: a }
                        };
                        this.universe.evolveUniverse(info);
                        throw new VoidEncounterSignal(info);
                    }
                    return a % b;
                });
            case 'EVIsVoid':
                const testValue = this.eval(expr.expr);
                return { type: 'VBool', value: testValue.type === 'VVoid' };
            case 'EVIfVoid':
                const condValue = this.eval(expr.condition);
                if (condValue.type === 'VVoid') {
                    return this.eval(expr.thenBranch);
                }
                else {
                    return this.eval(expr.elseBranch);
                }
            case 'EVDefault':
                const defaultValue = this.eval(expr.expr);
                if (defaultValue.type === 'VVoid') {
                    return this.eval(expr.fallback);
                }
                return defaultValue;
            case 'EVVar':
                return this.env.lookup(expr.name, this.universe);
            case 'EVLet':
                const boundValue = this.eval(expr.binding);
                const newEnv = this.env.bind(expr.name, boundValue);
                const newEvaluator = new EnhancedUnravelEvaluator(this.fuel, this.universe, newEnv);
                return newEvaluator.eval(expr.body);
            default:
                const _exhaustive = expr;
                throw new Error('Impossible: unhandled expression type');
        }
    }
    /**
     * Enhanced arithmetic with sophisticated void combination
     */
    evalArithmetic(left, right, operation, compute) {
        const leftVal = this.eval(left);
        const rightVal = this.eval(right);
        // Enhanced void propagation matching Haskell behavior
        if (leftVal.type === 'VVoid' && rightVal.type === 'VVoid') {
            // Combine voids with entropy accumulation
            const combinedInfo = this.universe.combineVoids(leftVal.info, rightVal.info);
            this.universe.evolveUniverse(combinedInfo);
            return { type: 'VVoid', info: combinedInfo };
        }
        if (leftVal.type === 'VVoid') {
            return leftVal; // Void propagates
        }
        if (rightVal.type === 'VVoid') {
            return rightVal; // Void propagates
        }
        // Type checking
        if (leftVal.type !== 'VNum' || rightVal.type !== 'VNum') {
            const info = {
                entropy: 1,
                timeStep: this.universe.timeStep,
                source: { type: VoidSourceType.TypeError, operation }
            };
            this.universe.evolveUniverse(info);
            return { type: 'VVoid', info };
        }
        // Safe computation
        try {
            const result = compute(leftVal.value, rightVal.value);
            return { type: 'VNum', value: result };
        }
        catch (e) {
            if (e instanceof VoidEncounterSignal) {
                return { type: 'VVoid', info: e.voidInfo };
            }
            throw e;
        }
    }
}
exports.EnhancedUnravelEvaluator = EnhancedUnravelEvaluator;
/**
 * Signal for void encounters (internal use)
 */
class VoidEncounterSignal extends Error {
    constructor(voidInfo) {
        super('Void encountered');
        this.voidInfo = voidInfo;
    }
}
// ============================================================================
// EXPRESSION BUILDERS (MATCHING HASKELL API)
// ============================================================================
exports.ev = {
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
    default: (expr, fallback) => ({ type: 'EVDefault', expr, fallback }),
    variable: (name) => ({ type: 'EVVar', name }),
    let: (name, binding, body) => ({ type: 'EVLet', name, binding, body })
};
// ============================================================================
// VOID FORENSICS (MATCHING HASKELL ANALYSIS)
// ============================================================================
class VoidForensics {
    static showVoidSource(source) {
        switch (source.type) {
            case VoidSourceType.DivByZero:
                return `DivByZero(${source.numerator})`;
            case VoidSourceType.ModByZero:
                return `ModByZero(${source.numerator})`;
            case VoidSourceType.UndefinedVar:
                return `UndefinedVar("${source.variable}")`;
            case VoidSourceType.OutOfFuel:
                return 'OutOfFuel';
            case VoidSourceType.TypeError:
                return `TypeError("${source.operation}")`;
            case VoidSourceType.VoidPropagation:
                return `VoidPropagation[${this.showVoidInfo(source.parent1)} + ${this.showVoidInfo(source.parent2)}]`;
        }
    }
    static showVoidInfo(info) {
        return `{e=${info.entropy},src=${this.showVoidSource(info.source)}}`;
    }
    static analyzeResult(value, universe) {
        switch (value.type) {
            case 'VNum':
                console.log(`  SUCCESS: ${value.value}`);
                break;
            case 'VBool':
                console.log(`  SUCCESS: ${value.value}`);
                break;
            case 'VVoid':
                console.log('  VOID DETECTED!');
                console.log(`    Entropy contribution: ${value.info.entropy}`);
                console.log(`    Failure time: step ${value.info.timeStep}`);
                console.log(`    Root cause: ${this.showVoidSource(value.info.source)}`);
                break;
        }
        console.log(`  Universe state: entropy=${universe.totalEntropy}, time=${universe.timeStep}, total_voids=${universe.voidCount}`);
    }
}
exports.VoidForensics = VoidForensics;
// ============================================================================
// EVALUATION HELPERS (MATCHING HASKELL API)
// ============================================================================
function runThermo(expr) {
    const universe = new EnhancedUniverse();
    const evaluator = new EnhancedUnravelEvaluator(1000, universe);
    const value = evaluator.eval(expr);
    return { value, universe };
}
function evalDefault(expr) {
    const result = runThermo(expr);
    return result.value;
}
// ============================================================================
// COMPREHENSIVE DEMO (MATCHING HASKELL EXAMPLES)
// ============================================================================
function runEnhancedDemo() {
    console.log('🌀 ENHANCED UNRAVEL TYPESCRIPT DEMO 🌀');
    console.log('Matching the sophisticated Haskell implementation\n');
    // ============================================================================
    // CALCULATION 1: Simple Division Chain (matching Haskell)
    // ============================================================================
    console.log('--- CALCULATION 1: Simple Division Chain ---');
    console.log('Computing: (100/10) + (50/5) + (20/0)');
    const calc1 = exports.ev.add(exports.ev.div(exports.ev.num(100), exports.ev.num(10)), exports.ev.add(exports.ev.div(exports.ev.num(50), exports.ev.num(5)), exports.ev.div(exports.ev.num(20), exports.ev.num(0))));
    const result1 = runThermo(calc1);
    VoidForensics.analyzeResult(result1.value, result1.universe);
    // ============================================================================
    // CALCULATION 2: Variable Dependencies (matching Haskell)
    // ============================================================================
    console.log('\n--- CALCULATION 2: Variable Dependencies ---');
    console.log('Computing: let x = 10/2, y = x/0, z = missing_var in x+y+z');
    const calc2 = exports.ev.let('x', exports.ev.div(exports.ev.num(10), exports.ev.num(2)), exports.ev.let('y', exports.ev.div(exports.ev.variable('x'), exports.ev.num(0)), exports.ev.let('z', exports.ev.variable('missing_var'), exports.ev.add(exports.ev.variable('x'), exports.ev.add(exports.ev.variable('y'), exports.ev.variable('z'))))));
    const result2 = runThermo(calc2);
    VoidForensics.analyzeResult(result2.value, result2.universe);
    // ============================================================================
    // CALCULATION 3: Cascading Failures (matching Haskell)
    // ============================================================================
    console.log('\n--- CALCULATION 3: Cascading Failures ---');
    console.log('Computing: Multiple errors combining');
    const calc3 = exports.ev.add(exports.ev.div(exports.ev.num(100), exports.ev.num(0)), // First void
    exports.ev.add(exports.ev.mod(exports.ev.num(50), exports.ev.num(0)), // Second void
    exports.ev.variable('undefined') // Third void
    ));
    const result3 = runThermo(calc3);
    VoidForensics.analyzeResult(result3.value, result3.universe);
    // ============================================================================
    // ENTROPY ACCUMULATION ANALYSIS (matching Haskell)
    // ============================================================================
    console.log('\n--- ENTROPY ACCUMULATION ANALYSIS ---');
    const simpleError = exports.ev.div(exports.ev.num(1), exports.ev.num(0));
    const doubleError = exports.ev.add(simpleError, simpleError);
    const tripleError = exports.ev.add(doubleError, simpleError);
    const getEntropy = (expr) => runThermo(expr).universe.totalEntropy;
    console.log('Entropy growth pattern:');
    console.log(`  1 error:  ${getEntropy(simpleError)} entropy`);
    console.log(`  2 errors: ${getEntropy(doubleError)} entropy`);
    console.log(`  3 errors: ${getEntropy(tripleError)} entropy`);
    // ============================================================================
    // FAILURE TYPE DISTRIBUTION (matching Haskell)
    // ============================================================================
    console.log('\n--- FAILURE TYPE DISTRIBUTION ---');
    const failures = [
        ['Division by zero', exports.ev.div(exports.ev.num(10), exports.ev.num(0))],
        ['Modulo by zero', exports.ev.mod(exports.ev.num(10), exports.ev.num(0))],
        ['Undefined variable', exports.ev.variable('ghost')],
        ['Type error', exports.ev.add(exports.ev.bool(true), exports.ev.num(5))], // This will cause TypeError
        ['Propagated void', exports.ev.add(exports.ev.div(exports.ev.num(1), exports.ev.num(0)), exports.ev.num(5))]
    ];
    console.log('Different failure types and their entropy:');
    failures.forEach(([desc, expr]) => {
        const result = runThermo(expr);
        console.log(`  ${desc}: entropy=${result.universe.totalEntropy}`);
        if (result.value.type === 'VVoid') {
            console.log(`    Source: ${VoidForensics.showVoidSource(result.value.info.source)}`);
        }
    });
    console.log('\n--- FINAL INSIGHTS ---');
    console.log('• Each failure type leaves a unique fingerprint');
    console.log('• Entropy accumulates non-linearly when voids combine');
    console.log('• The universe tracks every computational sin');
    console.log('• Void carries complete failure forensics');
    console.log('• Time advances even through failure');
    console.log('\n✨ The void remembers everything! ✨');
    console.log('\n=== UNRAVEL TYPESCRIPT: MATHEMATICAL SOPHISTICATION ===');
    console.log('✅ Non-linear entropy accumulation');
    console.log('✅ Rich void genealogy tracking');
    console.log('✅ Temporal failure analysis');
    console.log('✅ Variable environment integration');
    console.log('✅ Thermodynamic universe evolution');
    console.log('✅ Complete computational forensics');
    console.log('\n🌀 TypeScript Unravel: Matching Haskell sophistication! 🌀');
}
// Auto-run demo
if (typeof require !== 'undefined' && require.main === module) {
    runEnhancedDemo();
}
module.exports = {
    runEnhancedDemo,
    EnhancedUniverse,
    EnhancedUnravelEvaluator,
    VoidForensics,
    ev: exports.ev,
    runThermo,
    evalDefault
};
