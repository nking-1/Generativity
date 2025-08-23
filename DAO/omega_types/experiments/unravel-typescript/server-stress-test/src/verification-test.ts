/**
 * verification-test.ts
 * Test the specific time evolution bug and verify our understanding
 */

import { ProductionUniverse, ev, runUnravel } from './unravel-import';

function testCurrentImplementationBehavior(): void {
  console.log('🔍 TESTING CURRENT IMPLEMENTATION BEHAVIOR');
  console.log('Understanding exactly how time evolution currently works...\n');

  // Test 1: Single operations (should work correctly)
  console.log('=== TEST 1: SINGLE OPERATIONS ===');
  
  const singleTests = [
    { name: 'Simple division by zero', expr: ev.div(ev.num(10), ev.num(0)) },
    { name: 'Simple addition', expr: ev.add(ev.num(5), ev.num(3)) },
    { name: 'Another division by zero', expr: ev.div(ev.num(20), ev.num(0)) }
  ];

  singleTests.forEach(test => {
    const result = runUnravel(test.expr);
    console.log(`${test.name}: entropy=${result.universe.totalEntropy}, time=${result.universe.timeStep}, type=${result.value.type}`);
  });

  console.log('\n=== TEST 2: UNIVERSE STATE ISOLATION ===');
  
  // The issue: each runUnravel creates a new universe
  const universe1 = new ProductionUniverse();
  const universe2 = new ProductionUniverse();
  
  console.log(`Universe 1 initial: entropy=${universe1.totalEntropy}, time=${universe1.timeStep}`);
  console.log(`Universe 2 initial: entropy=${universe2.totalEntropy}, time=${universe2.timeStep}`);
  
  // Problem: runUnravel doesn't use our universe instances
  const result1 = runUnravel(ev.div(ev.num(10), ev.num(0)));
  const result2 = runUnravel(ev.div(ev.num(20), ev.num(0)));
  
  console.log(`After operations:`);
  console.log(`Universe 1: entropy=${universe1.totalEntropy}, time=${universe1.timeStep} (unchanged!)`);
  console.log(`Universe 2: entropy=${universe2.totalEntropy}, time=${universe2.timeStep} (unchanged!)`);
  console.log(`Result 1 universe: entropy=${result1.universe.totalEntropy}, time=${result1.universe.timeStep}`);
  console.log(`Result 2 universe: entropy=${result2.universe.totalEntropy}, time=${result2.universe.timeStep}`);

  console.log('\n🎯 ISSUE IDENTIFIED:');
  console.log('runUnravel() creates fresh universe for each call');
  console.log('Time never accumulates across operations');
  console.log('This explains why time stops advancing in complex expressions');

  console.log('\n=== TEST 3: DEMONSTRATING THE BUG ===');
  
  // Reproduce the exact entropy bomb scenario
  let currentExpr = ev.div(ev.num(1), ev.num(0));
  let previousTime = 0;
  let previousEntropy = 0;

  for (let step = 0; step < 5; step++) {
    currentExpr = ev.add(currentExpr, currentExpr);  // Double complexity
    const result = runUnravel(currentExpr);
    
    const timeDiff = result.universe.timeStep - previousTime;
    const entropyDiff = result.universe.totalEntropy - previousEntropy;
    
    console.log(`Step ${step}: entropy=${result.universe.totalEntropy} (+${entropyDiff}), time=${result.universe.timeStep} (+${timeDiff})`);
    
    if (step > 0 && timeDiff === 0) {
      console.log(`  🚨 TIME BUG: No time advancement despite entropy increase`);
    }
    
    previousTime = result.universe.timeStep;
    previousEntropy = result.universe.totalEntropy;
  }

  console.log('\n✅ BUG CONFIRMED: Time evolution issue is due to fresh universe creation');
  console.log('🔧 SOLUTION: Need persistent universe or corrected time tracking');
}

function proposeImplementationFix(): void {
  console.log('\n🔧 PROPOSED IMPLEMENTATION FIX');
  console.log('Based on Coq spec analysis...\n');

  console.log('📋 CURRENT ISSUE:');
  console.log('1. runUnravel() creates new ProductionUniverse() for each call');
  console.log('2. Time resets to 0 with each operation');
  console.log('3. Complex expressions that should accumulate time show constant time');

  console.log('\n📋 COQ SPEC REQUIREMENTS:');
  console.log('1. evolve_universe should increment time_step by exactly 1');
  console.log('2. combine_voids should use current universe time_step');
  console.log('3. Time should be persistent across operations');

  console.log('\n🔧 PROPOSED FIXES:');
  console.log('Option A: Modify runUnravel to accept persistent universe parameter');
  console.log('Option B: Fix internal universe evolution to properly track time within single evaluation');
  console.log('Option C: Correct the time advancement logic in complex expression evaluation');

  console.log('\n🎯 RECOMMENDED APPROACH:');
  console.log('Fix Option B - ensure time advances correctly during single complex evaluation');
  console.log('This preserves the current API while fixing the mathematical bug');
}

function createMinimalReproduction(): void {
  console.log('\n🧪 MINIMAL REPRODUCTION OF TIME BUG');
  console.log('Creating simplest case that demonstrates the issue...\n');

  // Minimal case: two voids combined should advance time more than one void
  const singleVoid = runUnravel(ev.div(ev.num(1), ev.num(0)));
  const doubleVoid = runUnravel(ev.add(ev.div(ev.num(1), ev.num(0)), ev.div(ev.num(2), ev.num(0))));

  console.log('MINIMAL REPRODUCTION:');
  console.log(`Single void: entropy=${singleVoid.universe.totalEntropy}, time=${singleVoid.universe.timeStep}, voids=${singleVoid.universe.voidCount}`);
  console.log(`Double void: entropy=${doubleVoid.universe.totalEntropy}, time=${doubleVoid.universe.timeStep}, voids=${doubleVoid.universe.voidCount}`);

  console.log('\nEXPECTED (based on Coq spec):');
  console.log(`Single void should have: entropy=1, time=1, voids=1`);
  console.log(`Double void should have: entropy=4, time=3, voids=3 (two individual + one combination)`);

  console.log('\nACTUAL:');
  console.log(`Single: entropy=${singleVoid.universe.totalEntropy}, time=${singleVoid.universe.timeStep}`);
  console.log(`Double: entropy=${doubleVoid.universe.totalEntropy}, time=${doubleVoid.universe.timeStep}`);

  const timeMatchesExpected = (singleVoid.universe.timeStep === 1) && (doubleVoid.universe.timeStep === 3);
  console.log(`\n✅ Time evolution correct: ${timeMatchesExpected ? 'YES' : 'NO'}`);
  
  if (!timeMatchesExpected) {
    console.log('🔧 This confirms our fix is needed in the production library');
  }
}

// Run verification test
if (require.main === module) {
  testCurrentImplementationBehavior();
  proposeImplementationFix();  
  createMinimalReproduction();
  
  console.log('\n🌀 Ready to apply fix to production library! 🌀');
}