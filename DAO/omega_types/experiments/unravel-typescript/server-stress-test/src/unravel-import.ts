/**
 * unravel-import.ts
 * Proper import of our production Unravel library for server stress testing
 */

// Import our compiled production library
const UnravelLib = require('../../lib/unravel-final.js');

// Re-export with proper TypeScript types
export interface VoidInfo {
  readonly entropy: number;
  readonly timeStep: number;
  readonly source: any;
  readonly pattern: string;
  readonly timestamp: number;
}

export interface UnravelValue {
  readonly type: 'VNum' | 'VVoid' | 'VBool';
  readonly value?: number | boolean;
  readonly info?: VoidInfo;
}

export interface UniverseResult {
  readonly value: UnravelValue;
  readonly universe: {
    readonly totalEntropy: number;
    readonly timeStep: number;
    readonly voidCount: number;
    readonly history: VoidInfo[];
    getHealthStatus(): string;
    reset(): void;
  };
}

// Export production library functions with type safety
export const ProductionUniverse: new() => UniverseResult['universe'] = UnravelLib.ProductionUniverse;
export const ev = UnravelLib.ev;
export const runUnravel: (expr: any) => UniverseResult = UnravelLib.runUnravel;
export const EquivalenceChecker = UnravelLib.EquivalenceChecker;
export const ProductionTesting = UnravelLib.ProductionTesting;
export const ProductionVoidForensics = UnravelLib.ProductionVoidForensics;

// Test import worked
console.log('✅ Production Unravel library imported successfully for server stress testing');

// Quick verification
const testUniverse = new ProductionUniverse();
const testExpr = ev.div(ev.num(10), ev.num(0));
const testResult = runUnravel(testExpr);

console.log(`📊 Library verification: 10÷0 → ${testResult.value.type}, entropy=${testResult.universe.totalEntropy}`);
console.log('🏭 Server will use ACTUAL production library for all operations\n');