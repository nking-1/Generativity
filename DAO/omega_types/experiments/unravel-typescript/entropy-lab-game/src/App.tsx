/**
 * App.tsx
 * Entropy Lab - React game using PRODUCTION Unravel library
 * Demonstrates total functional programming through interactive gameplay
 */

import React, { useState, useEffect, useCallback } from 'react';
import './App.css';

// Import our ACTUAL production library
const Unravel = require('./unravel-wrapper.js');
const { ProductionUniverse, ev, runUnravel, EquivalenceChecker, ProductionTesting } = Unravel;

interface PuzzleLevel {
  id: number;
  name: string;
  description: string;
  targetValue: number;
  maxEntropy: number;
  initialNumbers: number[];
  hint: string;
}

const PUZZLE_LEVELS: PuzzleLevel[] = [
  {
    id: 1,
    name: "First Contact with omega_veil",
    description: "Get 42 using our production library. See structured impossibility in action!",
    targetValue: 42,
    maxEntropy: 2,
    initialNumbers: [84, 126, 0, 2, 3],
    hint: "Try 84 ÷ 2 = 42. Then try 84 ÷ 0 to see how our library handles impossibility!"
  },
  {
    id: 2,
    name: "Conservation Law Challenge",
    description: "Demonstrate entropy conservation through recovery operations",
    targetValue: 100,
    maxEntropy: 3,
    initialNumbers: [200, 150, 0, 2, 5],
    hint: "Division by zero increases entropy, but recovery preserves it (mathematical law)!"
  },
  {
    id: 3,
    name: "Noether's Theorem Verification",
    description: "Show that equivalent expressions have identical entropy",
    targetValue: 60,
    maxEntropy: 0,
    initialNumbers: [20, 40, 30, 10],
    hint: "Use our library's EquivalenceChecker to verify 20+40 ≡ 40+20!"
  },
  {
    id: 4,
    name: "Production Library Stress Test",
    description: "Push our library to its limits with complex void combinations",
    targetValue: 999,
    maxEntropy: 10,
    initialNumbers: [100, 50, 25, 0, 0, 0],
    hint: "Create cascading failures and watch our library handle them gracefully!"
  }
];

const App: React.FC = () => {
  const [universe] = useState(() => new ProductionUniverse());
  const [currentLevel, setCurrentLevel] = useState(0);
  const [gameHistory, setGameHistory] = useState<string[]>([]);
  const [selectedNumbers, setSelectedNumbers] = useState<number[]>([]);
  const [currentResult, setCurrentResult] = useState<any>(null);
  const [score, setScore] = useState(0);
  const [showHint, setShowHint] = useState(false);
  const [libraryStats, setLibraryStats] = useState({
    mathTestsPassed: 0,
    equivalenceTests: 0,
    productionCalls: 0
  });

  const level = PUZZLE_LEVELS[currentLevel];

  const addToHistory = useCallback((message: string, isError: boolean = false) => {
    const timestamp = new Date().toLocaleTimeString();
    const entry = `[${timestamp}] ${message}`;
    setGameHistory(prev => [entry, ...prev.slice(0, 19)]);
  }, []);

  // Production library operations
  const performProductionDivision = useCallback(() => {
    if (selectedNumbers.length !== 2) return;
    
    const [a, b] = selectedNumbers;
    
    // Use ACTUAL production library
    const expr = ev.div(ev.num(a), ev.num(b));
    const result = runUnravel(expr);
    
    setLibraryStats(prev => ({ ...prev, productionCalls: prev.productionCalls + 1 }));
    
    setCurrentResult(result.value);
    
    if (result.value.type === 'VVoid') {
      addToHistory(`🏭 PRODUCTION: ${a} ÷ ${b} → VOID (${result.value.info.pattern})`, true);
      addToHistory(`🔬 Library entropy: ${result.universe.totalEntropy}, forensics: ${JSON.stringify(result.value.info.source)}`, true);
    } else {
      addToHistory(`🏭 PRODUCTION: ${a} ÷ ${b} = ${result.value.value}`);
    }
    
    setSelectedNumbers([]);
  }, [selectedNumbers, addToHistory]);

  const performProductionAddition = useCallback(() => {
    if (selectedNumbers.length < 1) return;
    
    // Use ACTUAL production library for addition
    let expr;
    if (selectedNumbers.length === 2) {
      expr = ev.add(ev.num(selectedNumbers[0]), ev.num(selectedNumbers[1]));
      addToHistory(`🏭 PRODUCTION: Adding ${selectedNumbers[0]} + ${selectedNumbers[1]} using library`);
    } else if (currentResult && currentResult.type === 'VNum') {
      expr = ev.add(ev.num(currentResult.value), ev.num(selectedNumbers[0]));
      addToHistory(`🏭 PRODUCTION: Adding result ${currentResult.value} + ${selectedNumbers[0]} using library`);
    } else {
      return;
    }
    
    const result = runUnravel(expr);
    setLibraryStats(prev => ({ ...prev, productionCalls: prev.productionCalls + 1 }));
    
    setCurrentResult(result.value);
    
    if (result.value.type === 'VVoid') {
      addToHistory(`🔬 Library returned VOID with entropy: ${result.universe.totalEntropy}`, true);
    } else {
      addToHistory(`✅ Library computed: ${result.value.value}`);
    }
    
    setSelectedNumbers([]);
  }, [selectedNumbers, currentResult, addToHistory]);

  const testLibraryMathematicalLaws = useCallback(() => {
    // Use ACTUAL production library testing
    const mathTest = ProductionTesting.testMathematicalLaws();
    
    setLibraryStats(prev => ({ 
      ...prev, 
      mathTestsPassed: prev.mathTestsPassed + (mathTest.passed ? 1 : 0)
    }));
    
    addToHistory(`🧮 PRODUCTION LIBRARY: Mathematical laws test ${mathTest.passed ? 'PASSED' : 'FAILED'}`);
    mathTest.details.forEach(detail => {
      addToHistory(`  📐 ${detail}`);
    });
    
    // Test equivalence using production library
    const equiv = EquivalenceChecker.areEquivalent(
      ev.add(ev.num(20), ev.num(30)),
      ev.add(ev.num(30), ev.num(20))
    );
    
    setLibraryStats(prev => ({ ...prev, equivalenceTests: prev.equivalenceTests + 1 }));
    addToHistory(`⚖️ PRODUCTION: Equivalence test ${equiv ? 'PASSED' : 'FAILED'} (Noether's theorem)`);
  }, [addToHistory]);

  const performLibraryRecovery = useCallback(() => {
    if (!currentResult || currentResult.type !== 'VVoid' || selectedNumbers.length !== 1) return;
    
    // Use production library's default/recovery mechanism
    const originalEntropy = universe.totalEntropy;
    const fallback = selectedNumbers[0];
    
    const recoveryExpr = ev.default(ev.void(), ev.num(fallback));
    const recoveryResult = runUnravel(recoveryExpr);
    
    setLibraryStats(prev => ({ ...prev, productionCalls: prev.productionCalls + 1 }));
    
    setCurrentResult(recoveryResult.value);
    
    // Verify conservation law from production library
    const entropyConserved = originalEntropy === recoveryResult.universe.totalEntropy;
    
    addToHistory(`🏭 PRODUCTION RECOVERY: VOID → ${fallback}`);
    addToHistory(`⚖️ Conservation law: ${entropyConserved ? 'VERIFIED' : 'VIOLATED'} (entropy ${originalEntropy} → ${recoveryResult.universe.totalEntropy})`);
    
    setSelectedNumbers([]);
  }, [currentResult, selectedNumbers, universe, addToHistory]);

  const resetLevel = useCallback(() => {
    universe.reset();
    setCurrentResult(null);
    setSelectedNumbers([]);
    addToHistory('🔄 Level reset - Production library universe returned to ground state');
  }, [universe, addToHistory]);

  // Check level completion
  useEffect(() => {
    if (currentResult && currentResult.type === 'VNum') {
      const achieved = currentResult.value === level.targetValue;
      const entropyOK = universe.totalEntropy <= level.maxEntropy;
      
      if (achieved && entropyOK) {
        setScore(prev => prev + 100 + (level.maxEntropy - universe.totalEntropy) * 10);
        addToHistory(`🎉 LEVEL COMPLETED using production library! Target: ${level.targetValue}, Entropy: ${universe.totalEntropy}/${level.maxEntropy}`);
        
        setTimeout(() => {
          if (currentLevel < PUZZLE_LEVELS.length - 1) {
            setCurrentLevel(prev => prev + 1);
            resetLevel();
          } else {
            addToHistory(`🏆 GAME COMPLETED! You've mastered our production Unravel library!`);
          }
        }, 2000);
      }
    }
  }, [currentResult, level, universe, currentLevel, resetLevel, addToHistory]);

  return (
    <div className="App">
      <header className="App-header">
        <h1>🧪 Entropy Lab</h1>
        <p>Interactive Demo of Production Unravel Library</p>
        <div className="game-stats">
          <span>Score: {score}</span>
          <span>Level: {currentLevel + 1}/{PUZZLE_LEVELS.length}</span>
          <span>Library Calls: {libraryStats.productionCalls}</span>
        </div>
      </header>

      <main className="game-container">
        {/* Library Status */}
        <div className="library-status">
          <h3>🏭 Production Library Status</h3>
          <div className="library-metrics">
            <div>📞 Library calls made: {libraryStats.productionCalls}</div>
            <div>🧮 Math tests passed: {libraryStats.mathTestsPassed}</div>
            <div>⚖️ Equivalence tests: {libraryStats.equivalenceTests}</div>
            <div>🌌 Universe entropy: {universe.totalEntropy}</div>
            <div>⏰ Universe time: {universe.timeStep}</div>
          </div>
        </div>

        {/* Level Info */}
        <div className="level-info">
          <h2>{level.name}</h2>
          <p>{level.description}</p>
          <div className="level-objectives">
            <span>Target: {level.targetValue}</span>
            <span>Max Entropy: {level.maxEntropy}</span>
          </div>
          {showHint && (
            <div className="hint">💡 {level.hint}</div>
          )}
          <button onClick={() => setShowHint(!showHint)} className="hint-btn">
            {showHint ? 'Hide Hint' : 'Show Hint'}
          </button>
        </div>

        {/* Current Result Display */}
        {currentResult && (
          <div className="current-result">
            <h3>🎯 Production Library Result</h3>
            {currentResult.type === 'VNum' ? (
              <div className="result-value">
                <span className="value">{currentResult.value}</span>
                {currentResult.value === level.targetValue && (
                  <span className="target-achieved">🎯 TARGET!</span>
                )}
              </div>
            ) : (
              <div className="result-void">
                <span className="void-indicator">⊥_ω (Library Void)</span>
                <div className="void-details">
                  <div>Library Pattern: {currentResult.info?.pattern}</div>
                  <div>Library Entropy: {currentResult.info?.entropy}</div>
                  <div>Library Source: {JSON.stringify(currentResult.info?.source)}</div>
                </div>
              </div>
            )}
          </div>
        )}

        {/* Number Selection */}
        <div className="number-selection">
          <h3>🔢 Available Numbers</h3>
          <div className="numbers-grid">
            {level.initialNumbers.map((num, index) => (
              <button
                key={index}
                className={`number-btn ${selectedNumbers.includes(num) ? 'selected' : ''}`}
                onClick={() => {
                  if (selectedNumbers.includes(num)) {
                    setSelectedNumbers(prev => prev.filter(n => n !== num));
                  } else if (selectedNumbers.length < 2) {
                    setSelectedNumbers(prev => [...prev, num]);
                  }
                }}
              >
                {num}
              </button>
            ))}
          </div>
          <div className="selected-numbers">
            Selected: {selectedNumbers.join(', ') || 'None'}
          </div>
        </div>

        {/* Production Library Operations */}
        <div className="operations">
          <h3>🏭 Production Library Operations</h3>
          <div className="operation-buttons">
            <button 
              onClick={performProductionDivision}
              disabled={selectedNumbers.length !== 2}
              className="operation-btn"
            >
              ➗ Library Divide
            </button>
            <button 
              onClick={performProductionAddition}
              disabled={selectedNumbers.length === 0}
              className="operation-btn"
            >
              ➕ Library Add
            </button>
            <button 
              onClick={performLibraryRecovery}
              disabled={!currentResult || currentResult.type !== 'VVoid' || selectedNumbers.length !== 1}
              className="operation-btn recovery-btn"
            >
              ✨ Library Recover
            </button>
            <button 
              onClick={testLibraryMathematicalLaws}
              className="operation-btn math-btn"
            >
              📐 Test Library Laws
            </button>
          </div>
        </div>

        {/* Game History showing library interactions */}
        <div className="game-history">
          <h3>📜 Production Library Interaction Log</h3>
          <div className="history-display">
            {gameHistory.map((entry, index) => (
              <div key={index} className="history-entry">
                {entry}
              </div>
            ))}
          </div>
        </div>

        {/* Game Controls */}
        <div className="game-controls">
          <button onClick={resetLevel} className="control-btn">
            🔄 Reset Universe
          </button>
          <button 
            onClick={() => {
              setCurrentLevel(0);
              resetLevel();
              setScore(0);
            }} 
            className="control-btn"
          >
            🏠 Restart Game
          </button>
          <button 
            onClick={() => {
              // Run comprehensive production library test
              addToHistory('🧪 Running production library comprehensive test...');
              try {
                Unravel.runProductionDemo();
                addToHistory('✅ Production library test completed successfully!');
              } catch (error: any) {
                addToHistory(`❌ Production library test failed: ${error.message}`, true);
              }
            }}
            className="control-btn"
          >
            🧪 Run Library Test Suite
          </button>
        </div>
      </main>
    </div>
  );
};

export default App;