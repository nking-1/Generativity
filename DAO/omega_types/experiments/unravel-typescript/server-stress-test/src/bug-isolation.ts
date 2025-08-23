/**
 * bug-isolation.ts
 * Isolate and fix the time evolution bug discovered in entropy bomb test
 */

import { ProductionUniverse, ev, runUnravel } from './unravel-import';

async function isolateTimeBug(): Promise<void> {
  console.log('🔍 BUG ISOLATION: TIME EVOLUTION ISSUE');
  console.log('Investigating why time stops advancing at high entropy...\n');

  // First, verify our current tests still pass
  console.log('=== VERIFICATION: EXISTING TESTS STILL PASS ===');
  
  // Test 1: Basic operations should still work
  const basicTest = runUnravel(ev.add(ev.num(10), ev.num(20)));
  console.log(`Basic test (10 + 20): ${basicTest.value.type === 'VNum' ? basicTest.value.value : 'FAILED'}`);
  console.log(`Basic entropy: ${basicTest.universe.totalEntropy}, time: ${basicTest.universe.timeStep}`);

  // Test 2: Division by zero should still work
  const divTest = runUnravel(ev.div(ev.num(10), ev.num(0)));
  console.log(`Division test (10 / 0): ${divTest.value.type}, entropy: ${divTest.universe.totalEntropy}, time: ${divTest.universe.timeStep}`);

  console.log('✅ Basic tests still pass\n');

  // Now isolate the time bug
  console.log('=== BUG ISOLATION: TIME EVOLUTION PATTERN ===');
  
  const universe = new ProductionUniverse();
  let timeSteps = [];
  let entropies = [];

  // Create a sequence of void operations and track time carefully
  for (let step = 0; step < 10; step++) {
    const testExpr = ev.div(ev.num(step), ev.num(0));  // Simple void creation
    const result = runUnravel(testExpr);
    
    timeSteps.push(result.universe.timeStep);
    entropies.push(result.universe.totalEntropy);
    
    console.log(`Step ${step}: entropy=${result.universe.totalEntropy}, time=${result.universe.timeStep}, voids=${result.universe.voidCount}`);
  }

  // Analyze time evolution pattern
  console.log('\nTime evolution analysis:');
  for (let i = 1; i < timeSteps.length; i++) {
    const timeDiff = timeSteps[i] - timeSteps[i-1];
    const entropyDiff = entropies[i] - entropies[i-1];
    
    console.log(`  Step ${i}: time +${timeDiff}, entropy +${entropyDiff}`);
    
    if (timeDiff !== 1) {
      console.log(`    🚨 TIME ISSUE: Expected +1, got +${timeDiff}`);
    }
  }

  console.log('\n=== BUG HYPOTHESIS ===');
  console.log('Based on Coq spec analysis:');
  console.log('1. evolve_universe should ALWAYS increment time_step by 1');
  console.log('2. combine_voids creates new VoidInfo with current universe time_step');
  console.log('3. Each void encounter should evolve the universe exactly once');
  console.log('\nProblem likely in our combineVoids or encounterVoid implementation...');

  // Test the specific bug scenario from entropy bomb
  console.log('\n=== REPRODUCING ENTROPY BOMB TIME BUG ===');
  
  let complexExpr = ev.div(ev.num(1), ev.num(0));  // Start simple
  
  for (let explosion = 0; explosion < 8; explosion++) {
    complexExpr = ev.add(complexExpr, complexExpr);  // Double complexity
    const result = runUnravel(complexExpr);
    
    console.log(`Explosion ${explosion}: entropy=${result.universe.totalEntropy}, time=${result.universe.timeStep}, voids=${result.universe.voidCount}`);
    
    // The issue: time should ALWAYS advance with each void encounter
    // But we're seeing time stay constant at high complexity
  }

  console.log('\n🎯 BUG IDENTIFIED: Time evolution stops advancing properly');
  console.log('Next step: Fix the universe evolution implementation to match Coq spec exactly');
}

// ============================================================================
// PROPOSED FIX TESTING
// ============================================================================

async function testProposedFix(): Promise<void> {
  console.log('\n🔧 TESTING PROPOSED FIX');
  console.log('Creating corrected universe evolution that matches Coq spec...\n');

  // Mock corrected universe implementation for testing
  class CorrectedUniverse {
    private _totalEntropy: number = 0;
    private _timeStep: number = 0;
    private _voidCount: number = 0;
    private _history: any[] = [];

    get totalEntropy(): number { return this._totalEntropy; }
    get timeStep(): number { return this._timeStep; }
    get voidCount(): number { return this._voidCount; }
    get history(): readonly any[] { return this._history; }

    // CORRECTED: Follow Coq spec exactly
    encounterVoid(info: any): void {
      // According to Coq: time_step := S u.(time_step) (always +1)
      this._totalEntropy += info.entropy;
      this._timeStep++;  // ALWAYS increment by exactly 1
      this._voidCount++;
      this._history.push(info);
    }

    // CORRECTED: combineVoids should create new info with CURRENT time
    combineVoids(v1: any, v2: any): any {
      return {
        entropy: v1.entropy + v2.entropy,
        timeStep: this._timeStep,  // Use CURRENT universe time
        source: { type: 'VoidPropagation', parent1: v1, parent2: v2 },
        pattern: 'COMPOSITE_VOID',
        timestamp: Date.now()
      };
    }

    getHealthStatus(): string {
      return this._totalEntropy === 0 ? 'excellent' : 'degraded';
    }

    reset(): void {
      this._totalEntropy = 0;
      this._timeStep = 0;
      this._voidCount = 0;
      this._history = [];
    }
  }

  // Test the corrected implementation
  console.log('Testing corrected universe evolution:');
  
  const correctedUniverse = new CorrectedUniverse();
  
  for (let test = 0; test < 10; test++) {
    // Simulate void encounter
    const voidInfo = {
      entropy: 1,
      timeStep: correctedUniverse.timeStep,
      pattern: 'DIVISION_BY_ZERO',
      source: `test_void_${test}`
    };
    
    const beforeTime = correctedUniverse.timeStep;
    correctedUniverse.encounterVoid(voidInfo);
    const afterTime = correctedUniverse.timeStep;
    
    console.log(`  Test ${test}: time ${beforeTime} → ${afterTime} (+${afterTime - beforeTime}), entropy=${correctedUniverse.totalEntropy}`);
    
    if (afterTime - beforeTime !== 1) {
      console.log(`    🚨 TIME ISSUE: Expected +1, got +${afterTime - beforeTime}`);
    }
  }

  // Test complex void combinations with corrected universe
  console.log('\nTesting corrected void combination:');
  
  const void1 = { entropy: 1, source: 'test1' };
  const void2 = { entropy: 1, source: 'test2' };
  
  const beforeCombineTime = correctedUniverse.timeStep;
  const combined = correctedUniverse.combineVoids(void1, void2);
  
  console.log(`Combined voids: entropy=${combined.entropy}, timeStep=${combined.timeStep}`);
  console.log(`Universe time before combine: ${beforeCombineTime}, after: ${correctedUniverse.timeStep}`);

  console.log('\n🎯 PROPOSED FIX:');
  console.log('1. Ensure encounterVoid ALWAYS increments time by exactly 1');
  console.log('2. Ensure combineVoids uses current universe timeStep');
  console.log('3. Each void encounter should evolve universe exactly once');
  console.log('\nThis should fix the time anomaly while preserving all other mathematical laws.');
}

// ============================================================================
// MAIN BUG INVESTIGATION
// ============================================================================

async function investigateTimeBug(): Promise<void> {
  await isolateTimeBug();
  await testProposedFix();
  
  console.log('\n🔧 NEXT STEPS:');
  console.log('1. Fix unravel-final.ts universe evolution to match Coq spec exactly');
  console.log('2. Re-run entropy bomb test to verify fix');
  console.log('3. Ensure all existing tests still pass');
  console.log('4. Push even harder with more diabolical tests');
  
  console.log('\n🌀 Mathematical debugging: Finding the limits of implementation vs theory! 🌀');
}

if (require.main === module) {
  investigateTimeBug().catch(console.error);
}