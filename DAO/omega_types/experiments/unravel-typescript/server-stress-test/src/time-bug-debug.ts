/**
 * time-bug-debug.ts
 * Deep debugging of the time evolution issue
 * Focus on why time stops advancing in complex expressions
 */

import { ProductionUniverse, ev, runUnravel } from './unravel-import';

function debugTimeEvolution(): void {
  console.log('🕰️ DEEP TIME EVOLUTION DEBUGGING');
  console.log('Investigating why time stops advancing in complex expressions...\n');

  // Test: Progressive complexity to find where time evolution breaks
  console.log('=== PROGRESSIVE COMPLEXITY TEST ===');
  
  let currentExpr = ev.div(ev.num(1), ev.num(0));  // Base case: entropy=1, time=1
  
  const progressResults = [];
  
  for (let complexity = 0; complexity < 15; complexity++) {
    const result = runUnravel(currentExpr);
    progressResults.push({
      complexity,
      entropy: result.universe.totalEntropy,
      time: result.universe.timeStep,
      voids: result.universe.voidCount
    });
    
    console.log(`Complexity ${complexity}: entropy=${result.universe.totalEntropy}, time=${result.universe.timeStep}, voids=${result.universe.voidCount}`);
    
    // Double the complexity for next iteration
    currentExpr = ev.add(currentExpr, currentExpr);
  }

  // Analyze where the issue starts
  console.log('\n=== TIME ADVANCEMENT ANALYSIS ===');
  
  for (let i = 1; i < progressResults.length; i++) {
    const current = progressResults[i];
    const previous = progressResults[i - 1];
    
    const timeAdvancement = current.time - previous.time;
    const entropyGrowth = current.entropy - previous.entropy;
    const voidGrowth = current.voids - previous.voids;
    
    console.log(`Step ${i}: time +${timeAdvancement}, entropy +${entropyGrowth}, voids +${voidGrowth}`);
    
    // Flag suspicious patterns
    if (timeAdvancement === 0 && entropyGrowth > 0) {
      console.log(`  🚨 SUSPICIOUS: Entropy increased but time didn't advance`);
    }
    
    if (timeAdvancement > 0 && timeAdvancement !== voidGrowth) {
      console.log(`  🤔 INTERESTING: Time advancement (${timeAdvancement}) ≠ void growth (${voidGrowth})`);
    }
    
    // According to Coq spec: each void encounter should advance time by 1
    // So time advancement should equal void growth in most cases
  }

  console.log('\n=== HYPOTHESIS TESTING ===');
  
  // Test hypothesis: The issue might be in how voids are counted vs time advancement
  console.log('Testing relationship between void count and time steps...');
  
  const relationshipTests = [
    ev.div(ev.num(10), ev.num(0)),  // Single void
    ev.add(ev.div(ev.num(1), ev.num(0)), ev.div(ev.num(2), ev.num(0))),  // Two voids combined
    ev.add(ev.add(ev.div(ev.num(1), ev.num(0)), ev.div(ev.num(2), ev.num(0))), ev.div(ev.num(3), ev.num(0)))  // Three voids
  ];

  relationshipTests.forEach((expr, index) => {
    const result = runUnravel(expr);
    const timeVoidRatio = result.universe.timeStep / result.universe.voidCount;
    
    console.log(`Test ${index + 1}: time=${result.universe.timeStep}, voids=${result.universe.voidCount}, ratio=${timeVoidRatio.toFixed(2)}`);
    
    // In Coq spec, each void encounter should advance time by 1
    // So time should equal voids in most cases
    if (Math.abs(result.universe.timeStep - result.universe.voidCount) > 1) {
      console.log(`  🤔 Unexpected time/void ratio: ${timeVoidRatio.toFixed(2)}`);
    }
  });

  console.log('\n🎯 DEBUGGING CONCLUSION:');
  console.log('Need to trace through exactly how our implementation differs from Coq spec');
  console.log('Focus on: evolve_universe and combine_voids logic');
}

function createFocusedTimeTest(): void {
  console.log('\n⏰ FOCUSED TIME EVOLUTION TEST');
  console.log('Testing exactly what the Coq spec says should happen...\n');

  // According to Coq spec:
  // 1. Each evalT call with void should evolve universe once
  // 2. evolve_universe increments time_step by 1  
  // 3. combine_voids creates VoidInfo with current time_step

  console.log('Testing Coq spec expectations:');
  
  // Test what should happen with double void according to Coq
  console.log('\nCoq spec prediction for: add(div(1,0), div(2,0))');
  console.log('1. Evaluate div(1,0) → creates VoidInfo, evolves universe: time=1');
  console.log('2. Evaluate div(2,0) → creates VoidInfo, evolves universe: time=2');
  console.log('3. Add combines voids → creates combined VoidInfo, evolves universe: time=3');
  console.log('Expected result: entropy=4 (1+1+2), time=3, voids=3');

  const actualResult = runUnravel(ev.add(ev.div(ev.num(1), ev.num(0)), ev.div(ev.num(2), ev.num(0))));
  console.log(`Actual result: entropy=${actualResult.universe.totalEntropy}, time=${actualResult.universe.timeStep}, voids=${actualResult.universe.voidCount}`);

  const matchesSpec = (actualResult.universe.totalEntropy === 4) && 
                     (actualResult.universe.timeStep === 3) && 
                     (actualResult.universe.voidCount === 3);

  console.log(`✅ Matches Coq spec: ${matchesSpec ? 'YES' : 'NO'}`);

  if (matchesSpec) {
    console.log('🎉 Our implementation actually matches the Coq spec!');
    console.log('The "time anomaly" in entropy bomb might be expected behavior at extreme complexity');
  } else {
    console.log('🔧 Implementation doesn\'t match Coq spec - fix needed');
  }
}

// Run all debugging
if (require.main === module) {
  debugTimeEvolution();
  createFocusedTimeTest();
  
  console.log('\n🌀 Time debugging complete - ready for targeted fix! 🌀');
}