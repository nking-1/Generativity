/**
 * unravel-core.ts
 * Import and adapt our production Unravel library for React game
 * This ensures we're testing the actual library, not a copy
 */

// Import from our production implementation
import { 
  ProductionUniverse,
  ProductionUnravelEvaluator, 
  ev,
  runUnravel,
  UnravelExpr,
  UnravelValue,
  VoidInfo as ProductionVoidInfo,
  ImpossibilityPattern
} from '../unravel-final';

// Re-export production types for game use
export { ProductionUniverse as GameUniverse };
export type { ProductionVoidInfo as VoidInfo };

// Adapt production types for game
export interface UniverseState {
  readonly totalEntropy: number;
  readonly timeStep: number; 
  readonly voidCount: number;
  readonly history: ProductionVoidInfo[];
}

// Game-specific wrapper functions that use our production library
export type GameValue = UnravelValue;

export function safeDiv(a: number, b: number, universe: ProductionUniverse): GameValue {
  // Use our production library's expression evaluation
  const expr = ev.div(ev.num(a), ev.num(b));
  const result = runUnravel(expr);
  
  // Update the passed universe with the result
  if (result.value.type === 'VVoid') {
    universe.encounterVoid(result.value.info);
  }
  
  return result.value;
}

export function safeAdd(a: GameValue, b: GameValue, universe: ProductionUniverse): GameValue {
  // Convert GameValues to expressions and use production library
  const aExpr = a.type === 'VNum' ? ev.num(a.value) : ev.void();
  const bExpr = b.type === 'VNum' ? ev.num(b.value) : ev.void();
  
  const expr = ev.add(aExpr, bExpr);
  const result = runUnravel(expr);
  
  // Update universe
  if (result.value.type === 'VVoid') {
    universe.encounterVoid(result.value.info);
  }
  
  return result.value;
}

export function recover(value: GameValue, fallback: number): GameValue {
  // Recovery preserves entropy (conservation law from production library)
  if (value.type === 'VVoid') {
    return { type: 'VNum', value: fallback };
  }
  return value;
}

export function unwrapOr(value: GameValue, fallback: number): number {
  return value.type === 'VNum' ? value.value : fallback;
}

// Game-specific helpers
export function createGameExpression(
  operation: 'add' | 'div' | 'mod',
  a: number,
  b: number
): UnravelExpr {
  switch (operation) {
    case 'add': return ev.add(ev.num(a), ev.num(b));
    case 'div': return ev.div(ev.num(a), ev.num(b));
    case 'mod': return ev.mod(ev.num(a), ev.num(b));
  }
}

export function evaluateWithUniverse(
  expr: UnravelExpr,
  universe: ProductionUniverse
): GameValue {
  const result = runUnravel(expr);
  
  // Sync universe state
  if (result.value.type === 'VVoid') {
    universe.encounterVoid(result.value.info);
  }
  
  return result.value;
}