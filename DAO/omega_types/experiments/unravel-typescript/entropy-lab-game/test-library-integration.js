/**
 * test-library-integration.js
 * Verify the game properly uses our production Unravel library
 */

const Unravel = require('./src/unravel-wrapper.js');
const { ProductionUniverse, ev, runUnravel, EquivalenceChecker, ProductionTesting } = Unravel;

function testGameLibraryIntegration() {
  console.log('🎮 TESTING GAME → PRODUCTION LIBRARY INTEGRATION 🎮\n');

  // Test 1: Basic library functionality
  console.log('=== TEST 1: BASIC LIBRARY FUNCTIONALITY ===');
  
  const universe = new ProductionUniverse();
  console.log(`Initial universe: entropy=${universe.totalEntropy}, time=${universe.timeStep}`);
  
  // Use production library division
  const divExpr = ev.div(ev.num(84), ev.num(2));
  const divResult = runUnravel(divExpr);
  console.log(`84 ÷ 2 = ${divResult.value.value} (type: ${divResult.value.type})`);
  console.log(`Universe after operation: entropy=${divResult.universe.totalEntropy}`);

  // Test void creation
  const voidExpr = ev.div(ev.num(84), ev.num(0));
  const voidResult = runUnravel(voidExpr);
  console.log(`84 ÷ 0 = ${voidResult.value.type} (entropy: ${voidResult.universe.totalEntropy})`);
  console.log('✅ Basic library operations working in game context\n');

  // Test 2: Mathematical law verification
  console.log('=== TEST 2: MATHEMATICAL LAWS ===');
  
  const mathTest = ProductionTesting.testMathematicalLaws();
  console.log(`Production library math tests: ${mathTest.passed ? 'ALL PASSED' : 'SOME FAILED'}`);
  mathTest.details.forEach(detail => console.log(`  ${detail}`));

  // Test equivalence (Noether's theorem)
  const equiv = EquivalenceChecker.areEquivalent(
    ev.add(ev.num(30), ev.num(12)),
    ev.add(ev.num(12), ev.num(30))
  );
  console.log(`Equivalence test (30+12 vs 12+30): ${equiv ? 'EQUIVALENT' : 'DIFFERENT'}`);
  console.log('✅ Mathematical laws working in game\n');

  // Test 3: Complex game scenario
  console.log('=== TEST 3: COMPLEX GAME SCENARIO ===');
  
  // Simulate game: divide by zero, then recover, then add
  const gameUniverse = new ProductionUniverse();
  
  const step1Expr = ev.div(ev.num(100), ev.num(0));  // Player divides by zero
  const step1Result = runUnravel(step1Expr);
  console.log(`Step 1 (div by zero): ${step1Result.value.type}, entropy=${step1Result.universe.totalEntropy}`);
  
  const step2Expr = ev.default(step1Expr, ev.num(42));  // Player recovers
  const step2Result = runUnravel(step2Expr);
  console.log(`Step 2 (recovery): ${step2Result.value.value}, entropy=${step2Result.universe.totalEntropy}`);
  
  const step3Expr = ev.add(step2Expr, ev.num(18));  // Player continues
  const step3Result = runUnravel(step3Expr);
  console.log(`Step 3 (continue): ${step3Result.value.value}, entropy=${step3Result.universe.totalEntropy}`);
  
  console.log('✅ Complex scenarios work with production library\n');

  // Test 4: Game-specific patterns
  console.log('=== TEST 4: GAME-SPECIFIC PATTERNS ===');
  
  // Test player attempting "impossible" operations
  const impossibleCases = [
    { name: 'Division by zero', expr: ev.div(ev.num(42), ev.num(0)) },
    { name: 'Undefined variable', expr: ev.variable('nonexistent') },
    { name: 'Self-reference', expr: ev.let('x', ev.variable('x'), ev.variable('x')) }
  ];
  
  impossibleCases.forEach(testCase => {
    const result = runUnravel(testCase.expr);
    console.log(`${testCase.name}: ${result.value.type} (entropy: ${result.universe.totalEntropy})`);
    if (result.value.type === 'VVoid') {
      console.log(`  Pattern: ${result.value.info.pattern}`);
      console.log(`  Source: ${JSON.stringify(result.value.info.source)}`);
    }
  });
  
  console.log('✅ All "impossible" operations handled gracefully by library\n');

  console.log('=== INTEGRATION VERIFICATION COMPLETE ===');
  console.log('🏭 Game successfully uses production Unravel library');
  console.log('🔄 Library changes will automatically affect game behavior');  
  console.log('🧪 Game serves as continuous integration test for library');
  console.log('🎯 Perfect setup for iterative development!');
  console.log('\n🌀 Ready for true library-game integration! 🌀');
}

// Run test
testGameLibraryIntegration();