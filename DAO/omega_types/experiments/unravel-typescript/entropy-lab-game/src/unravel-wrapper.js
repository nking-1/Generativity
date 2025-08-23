/**
 * unravel-wrapper.js
 * Wrapper to import our compiled production Unravel library
 * This ensures the game uses the ACTUAL library, not a copy
 */

// Import our compiled production library
const UnravelLib = require('../../lib/unravel-final.js');

// Re-export everything the game needs
module.exports = {
  // Core classes from production library
  ProductionUniverse: UnravelLib.ProductionUniverse,
  ProductionUnravelEvaluator: UnravelLib.ProductionUnravelEvaluator,
  EquivalenceChecker: UnravelLib.EquivalenceChecker,
  ProductionTesting: UnravelLib.ProductionTesting,
  ProductionVoidForensics: UnravelLib.ProductionVoidForensics,
  
  // Expression builders
  ev: UnravelLib.ev,
  
  // Evaluation functions
  runUnravel: UnravelLib.runUnravel,
  evalUnravel: UnravelLib.evalUnravel,
  
  // Enums
  ImpossibilityPattern: UnravelLib.ImpossibilityPattern,
  
  // Main export
  default: UnravelLib.default,
  
  // Test functions
  runProductionDemo: UnravelLib.runProductionDemo
};