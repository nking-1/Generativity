/**
 * fixed-implementation.ts
 * Corrected implementation that properly maintains universe state
 * Fixes the time evolution bug by using persistent universe
 */

// ============================================================================
// CORRECTED UNIVERSE IMPLEMENTATION (MATCHING COQ SPEC)
// ============================================================================

interface VoidInfo {
  readonly entropy: number;
  readonly timeStep: number;
  readonly source: any;
  readonly pattern: string;
  readonly timestamp: number;
}

/**
 * Fixed universe that maintains state across operations
 * IMPLEMENTS: Universe record from Coq spec exactly
 */
class FixedUniverse {
  private _totalEntropy: number = 0;
  private _timeStep: number = 0;
  private _voidCount: number = 0;
  private _history: VoidInfo[] = [];

  get totalEntropy(): number { return this._totalEntropy; }
  get timeStep(): number { return this._timeStep; }
  get voidCount(): number { return this._voidCount; }
  get history(): readonly VoidInfo[] { return this._history; }

  /**
   * CORRECTED: evolve_universe from Coq spec
   * ALWAYS increments time_step by exactly 1
   */
  encounterVoid(info: VoidInfo): void {
    // Match Coq spec exactly:
    this._totalEntropy += info.entropy;  // total_entropy := u.(total_entropy) + entropy
    this._timeStep++;                    // time_step := S u.(time_step) [ALWAYS +1]
    this._voidCount++;                   // void_count := S u.(void_count)
    this._history.push(info);
  }

  /**
   * CORRECTED: combine_voids from Coq spec  
   * Uses current universe time_step
   */
  combineVoids(v1: VoidInfo, v2: VoidInfo): VoidInfo {
    // Match Coq spec: VInfo (e1 + e2) u.(time_step) (VoidPropagation v1 v2)
    return {
      entropy: v1.entropy + v2.entropy,   // e1 + e2
      timeStep: this._timeStep,           // u.(time_step) - use CURRENT time
      source: { type: 'VoidPropagation', parent1: v1, parent2: v2 },
      pattern: 'COMPOSITE_VOID',
      timestamp: Date.now()
    };
  }

  getHealthStatus(): string {
    if (this._totalEntropy === 0) return 'excellent';
    if (this._totalEntropy < 5) return 'good';
    if (this._totalEntropy < 15) return 'warning';
    return 'critical';
  }

  reset(): void {
    this._totalEntropy = 0;
    this._timeStep = 0;
    this._voidCount = 0;
    this._history = [];
  }
}

/**
 * Fixed evaluator that uses persistent universe
 */
class FixedEvaluator {
  constructor(private fuel: number, private universe: FixedUniverse) {}

  eval(expr: any): any {
    if (this.fuel <= 0) {
      const info: VoidInfo = {
        entropy: 1,
        timeStep: this.universe.timeStep,
        source: { type: 'OutOfFuel' },
        pattern: 'OUT_OF_FUEL',
        timestamp: Date.now()
      };
      this.universe.encounterVoid(info);  // This increments time
      return { type: 'VVoid', info };
    }

    this.fuel--;

    // Simplified eval for testing
    if (expr.type === 'EVNum') {
      return { type: 'VNum', value: expr.value };
    }

    if (expr.type === 'EVDiv') {
      const leftVal = this.eval(expr.left);
      const rightVal = this.eval(expr.right);

      if (leftVal.type === 'VNum' && rightVal.type === 'VNum' && rightVal.value === 0) {
        const info: VoidInfo = {
          entropy: 1,
          timeStep: this.universe.timeStep,
          source: { type: 'DivByZero', numerator: leftVal.value },
          pattern: 'DIVISION_BY_ZERO',
          timestamp: Date.now()
        };
        this.universe.encounterVoid(info);  // This increments time
        return { type: 'VVoid', info };
      }

      if (leftVal.type === 'VNum' && rightVal.type === 'VNum') {
        return { type: 'VNum', value: Math.floor(leftVal.value / rightVal.value) };
      }

      // Handle void propagation
      return { type: 'VVoid', info: { entropy: 1, timeStep: this.universe.timeStep, source: 'void_prop', pattern: 'VOID_PROP', timestamp: Date.now() }};
    }

    if (expr.type === 'EVAdd') {
      const leftVal = this.eval(expr.left);
      const rightVal = this.eval(expr.right);

      if (leftVal.type === 'VVoid' && rightVal.type === 'VVoid') {
        // CORRECTED: Use persistent universe for combination
        const combined = this.universe.combineVoids(leftVal.info, rightVal.info);
        this.universe.encounterVoid(combined);  // This increments time
        return { type: 'VVoid', info: combined };
      }

      if (leftVal.type === 'VVoid') return leftVal;
      if (rightVal.type === 'VVoid') return rightVal;

      if (leftVal.type === 'VNum' && rightVal.type === 'VNum') {
        return { type: 'VNum', value: leftVal.value + rightVal.value };
      }
    }

    return { type: 'VVoid', info: { entropy: 1, timeStep: this.universe.timeStep, source: 'unknown', pattern: 'UNKNOWN', timestamp: Date.now() }};
  }
}

// Helper expression builders
const fev = {
  num: (value: number) => ({ type: 'EVNum', value }),
  div: (left: any, right: any) => ({ type: 'EVDiv', left, right }),
  add: (left: any, right: any) => ({ type: 'EVAdd', left, right })
};

// ============================================================================
// TEST THE FIX
// ============================================================================

async function testFixedImplementation(): Promise<void> {
  console.log('🔧 TESTING FIXED IMPLEMENTATION');
  console.log('Verifying that time evolution now works correctly...\n');

  const fixedUniverse = new FixedUniverse();
  const evaluator = new FixedEvaluator(1000, fixedUniverse);

  console.log('=== CORRECTED TIME EVOLUTION TEST ===');
  
  // Test sequence of operations with persistent universe
  const operations = [
    { name: 'First division by zero', expr: fev.div(fev.num(10), fev.num(0)) },
    { name: 'Second division by zero', expr: fev.div(fev.num(20), fev.num(0)) },
    { name: 'Combine the voids', expr: fev.add(fev.div(fev.num(1), fev.num(0)), fev.div(fev.num(2), fev.num(0))) },
    { name: 'Another void', expr: fev.div(fev.num(30), fev.num(0)) },
    { name: 'Complex combination', expr: fev.add(fev.add(fev.div(fev.num(1), fev.num(0)), fev.div(fev.num(2), fev.num(0))), fev.div(fev.num(3), fev.num(0))) }
  ];

  operations.forEach((op, index) => {
    const beforeTime = fixedUniverse.timeStep;
    const beforeEntropy = fixedUniverse.totalEntropy;
    
    const result = evaluator.eval(op.expr);
    
    const afterTime = fixedUniverse.timeStep;
    const afterEntropy = fixedUniverse.totalEntropy;
    const timeDiff = afterTime - beforeTime;
    const entropyDiff = afterEntropy - beforeEntropy;
    
    console.log(`${index + 1}. ${op.name}:`);
    console.log(`   Before: time=${beforeTime}, entropy=${beforeEntropy}`);
    console.log(`   After:  time=${afterTime}, entropy=${afterEntropy}`);
    console.log(`   Change: time +${timeDiff}, entropy +${entropyDiff}`);
    
    if (result.type === 'VVoid') {
      console.log(`   Result: VOID (${result.info.pattern})`);
    } else {
      console.log(`   Result: ${result.value}`);
    }
    
    // Time should advance for void operations
    if (result.type === 'VVoid' && timeDiff === 0) {
      console.log(`   🚨 TIME BUG: Void operation didn't advance time!`);
    } else if (result.type === 'VVoid' && timeDiff > 0) {
      console.log(`   ✅ Time advanced correctly for void operation`);
    }
    
    console.log();
  });

  console.log('=== ENTROPY BOMB REPRODUCTION WITH FIX ===');
  
  // Test the entropy bomb scenario with fixed implementation
  let bombExpr = fev.div(fev.num(1), fev.num(0));
  
  for (let explosion = 0; explosion < 8; explosion++) {
    bombExpr = fev.add(bombExpr, bombExpr);
    
    const beforeTime = fixedUniverse.timeStep;
    const result = evaluator.eval(bombExpr);
    const afterTime = fixedUniverse.timeStep;
    
    console.log(`Fixed explosion ${explosion}: entropy=${fixedUniverse.totalEntropy}, time=${afterTime} (+${afterTime - beforeTime}), voids=${fixedUniverse.voidCount}`);
  }

  console.log('\n🎯 CONCLUSION:');
  console.log('The fix shows that time should advance with each void encounter.');
  console.log('The original bug was likely in how we handle universe state between operations.');
  console.log('Next: Apply this fix to production library and re-test!');
}

if (require.main === module) {
  testFixedImplementation().catch(console.error);
}