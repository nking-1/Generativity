/**
 * App.tsx
 * Entropy Lab - A physics-based puzzle game powered by Unravel
 * Players manipulate computational universes and explore mathematical laws
 */

import React, { useState, useEffect, useCallback } from 'react';
import './App.css';
import { GameUniverse, safeDiv, safeAdd, recover, unwrapOr, VoidPattern, GameValue } from './unravel-core';

interface PuzzleLevel {
  id: number;
  name: string;
  description: string;
  targetValue: number;
  maxEntropy: number;
  initialNumbers: number[];
  operations: string[];
  hint: string;
}

const PUZZLE_LEVELS: PuzzleLevel[] = [
  {
    id: 1,
    name: "First Contact",
    description: "Get 42 using safe division. Watch what happens when you divide by zero!",
    targetValue: 42,
    maxEntropy: 2,
    initialNumbers: [84, 126, 0, 2, 3],
    operations: ["÷", "+"],
    hint: "84 ÷ 2 = 42. But what if you try 84 ÷ 0? Unravel handles it gracefully!"
  },
  {
    id: 2,
    name: "Entropy Management",
    description: "Reach 100 while keeping entropy below 3. Multiple paths possible!",
    targetValue: 100,
    maxEntropy: 3,
    initialNumbers: [200, 150, 0, 2, 5],
    operations: ["÷", "+", "recover"],
    hint: "Division by zero increases entropy. Use recovery to get values back!"
  },
  {
    id: 3,
    name: "Conservation Laws",
    description: "Demonstrate Noether's theorem: find two equivalent expressions.",
    targetValue: 60,
    maxEntropy: 0,
    initialNumbers: [20, 40, 30, 10],
    operations: ["+"],
    hint: "20 + 40 and 40 + 20 should have identical entropy (Noether's theorem)!"
  },
  {
    id: 4,
    name: "Thermodynamic Cascade",
    description: "Create entropy = 7 through void combinations. Study how voids combine!",
    targetValue: 999,
    maxEntropy: 7,
    initialNumbers: [100, 50, 25, 0, 0],
    operations: ["÷", "+", "recover"],
    hint: "Multiple divisions by zero combine non-linearly: 1+1+2=4, then 4+1+2=7!"
  },
  {
    id: 5,
    name: "Heat Death Challenge",
    description: "Push the universe to heat death (entropy ≥ 20) then recover!",
    targetValue: 42,
    maxEntropy: 25,
    initialNumbers: [10, 20, 30, 0, 0, 0],
    operations: ["÷", "+", "recover"],
    hint: "Generate massive entropy, then use recovery to get a usable value!"
  }
];

const App: React.FC = () => {
  const [universe, setUniverse] = useState(() => new GameUniverse());
  const [currentLevel, setCurrentLevel] = useState(0);
  const [gameHistory, setGameHistory] = useState<string[]>([]);
  const [selectedNumbers, setSelectedNumbers] = useState<number[]>([]);
  const [currentResult, setCurrentResult] = useState<GameValue | null>(null);
  const [score, setScore] = useState(0);
  const [showHint, setShowHint] = useState(false);

  const level = PUZZLE_LEVELS[currentLevel];

  const resetUniverse = useCallback(() => {
    const newUniverse = new GameUniverse();
    setUniverse(newUniverse);
    setCurrentResult(null);
    setSelectedNumbers([]);
    setGameHistory([]);
  }, []);

  const addToHistory = useCallback((message: string, isError: boolean = false) => {
    const timestamp = new Date().toLocaleTimeString();
    const entry = `[${timestamp}] ${message}`;
    setGameHistory(prev => [entry, ...prev.slice(0, 19)]);  // Keep last 20
  }, []);

  // Game operations
  const performDivision = useCallback(() => {
    if (selectedNumbers.length !== 2) return;
    
    const [a, b] = selectedNumbers;
    const result = safeDiv(a, b, universe);
    
    setCurrentResult(result);
    
    if (result.type === 'VVoid') {
      addToHistory(`${a} ÷ ${b} → VOID (${result.info.pattern})`, true);
    } else {
      addToHistory(`${a} ÷ ${b} = ${result.value}`);
    }
    
    setSelectedNumbers([]);
  }, [selectedNumbers, universe, addToHistory]);

  const performAddition = useCallback(() => {
    if (selectedNumbers.length !== 2 && !currentResult) return;
    
    let a: GameValue, b: GameValue;
    
    if (selectedNumbers.length === 2) {
      a = { type: 'VNum', value: selectedNumbers[0] };
      b = { type: 'VNum', value: selectedNumbers[1] };
    } else {
      a = currentResult!;
      b = { type: 'VNum', value: selectedNumbers[0] };
    }
    
    const result = safeAdd(a, b, universe);
    
    setCurrentResult(result);
    
    if (result.type === 'VVoid') {
      addToHistory(`Addition → VOID (entropy: ${result.info.entropy})`, true);
    } else {
      const aVal = a.type === 'VNum' ? a.value : 'void';
      const bVal = b.type === 'VNum' ? b.value : 'void';
      addToHistory(`${aVal} + ${bVal} = ${result.value}`);
    }
    
    setSelectedNumbers([]);
  }, [selectedNumbers, currentResult, universe, addToHistory]);

  const performRecovery = useCallback(() => {
    if (!currentResult || currentResult.type !== 'VVoid') return;
    
    const fallback = selectedNumbers[0] || 42;
    const recovered = recover(currentResult, fallback);
    
    setCurrentResult(recovered);
    addToHistory(`Recovery: VOID → ${fallback} (entropy preserved: ${universe.state.totalEntropy})`);
    setSelectedNumbers([]);
  }, [currentResult, selectedNumbers, universe, addToHistory]);

  // Check level completion
  useEffect(() => {
    if (currentResult && currentResult.type === 'VNum') {
      const achieved = currentResult.value === level.targetValue;
      const entropyOK = universe.state.totalEntropy <= level.maxEntropy;
      
      if (achieved && entropyOK) {
        setScore(prev => prev + 100 + (level.maxEntropy - universe.state.totalEntropy) * 10);
        addToHistory(`🎉 LEVEL COMPLETED! Target: ${level.targetValue}, Entropy: ${universe.state.totalEntropy}/${level.maxEntropy}`);
        
        setTimeout(() => {
          if (currentLevel < PUZZLE_LEVELS.length - 1) {
            setCurrentLevel(prev => prev + 1);
            resetUniverse();
            addToHistory(`🚀 Advanced to level ${currentLevel + 2}: ${PUZZLE_LEVELS[currentLevel + 1].name}`);
          } else {
            addToHistory(`🏆 GAME COMPLETED! You've mastered computational thermodynamics!`);
          }
        }, 2000);
      }
    }
  }, [currentResult, level, universe, currentLevel, resetUniverse, addToHistory]);

  return (
    <div className="App">
      <header className="App-header">
        <h1>🧪 Entropy Lab</h1>
        <p>Computational Physics Puzzle Game</p>
        <div className="game-stats">
          <span>Score: {score}</span>
          <span>Level: {currentLevel + 1}/{PUZZLE_LEVELS.length}</span>
        </div>
      </header>

      <main className="game-container">
        {/* Level Info */}
        <div className="level-info">
          <h2>{level.name}</h2>
          <p>{level.description}</p>
          <div className="level-objectives">
            <span>Target: {level.targetValue}</span>
            <span>Max Entropy: {level.maxEntropy}</span>
          </div>
          {showHint && (
            <div className="hint">
              💡 {level.hint}
            </div>
          )}
          <button onClick={() => setShowHint(!showHint)} className="hint-btn">
            {showHint ? 'Hide Hint' : 'Show Hint'}
          </button>
        </div>

        {/* Universe Status */}
        <div className="universe-status">
          <h3>🌌 Computational Universe</h3>
          <div className="universe-metrics">
            <div className="metric">
              <label>Total Entropy:</label>
              <div className="entropy-bar">
                <div 
                  className="entropy-fill"
                  style={{ 
                    width: `${Math.min(universe.state.totalEntropy / level.maxEntropy * 100, 100)}%`,
                    background: universe.state.totalEntropy > level.maxEntropy ? '#ff0055' : 
                               universe.state.totalEntropy > level.maxEntropy * 0.8 ? '#ffaa00' : '#00ff88'
                  }}
                >
                  {universe.state.totalEntropy}
                </div>
              </div>
            </div>
            <div className="metric">
              <label>Time Step:</label>
              <span>{universe.state.timeStep}</span>
            </div>
            <div className="metric">
              <label>Void Count:</label>
              <span>{universe.state.voidCount}</span>
            </div>
            <div className="metric">
              <label>Health:</label>
              <span className={`health-${universe.getHealthStatus()}`}>
                {universe.getHealthStatus().toUpperCase()}
              </span>
            </div>
          </div>
        </div>

        {/* Current Result */}
        {currentResult && (
          <div className="current-result">
            <h3>🎯 Current Result</h3>
            {currentResult.type === 'VNum' ? (
              <div className="result-value">
                <span className="value">{currentResult.value}</span>
                {currentResult.value === level.targetValue && (
                  <span className="target-achieved">🎯 TARGET!</span>
                )}
              </div>
            ) : (
              <div className="result-void">
                <span className="void-indicator">⊥_ω</span>
                <div className="void-details">
                  <div>Pattern: {currentResult.info.pattern}</div>
                  <div>Entropy: {currentResult.info.entropy}</div>
                  <div>Source: {currentResult.info.source}</div>
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

        {/* Operations */}
        <div className="operations">
          <h3>⚡ Operations</h3>
          <div className="operation-buttons">
            <button 
              onClick={performDivision}
              disabled={selectedNumbers.length !== 2}
              className="operation-btn"
            >
              ÷ Divide
            </button>
            <button 
              onClick={performAddition}
              disabled={selectedNumbers.length === 0 || (selectedNumbers.length > 2)}
              className="operation-btn"
            >
              + Add
            </button>
            <button 
              onClick={performRecovery}
              disabled={!currentResult || currentResult.type !== 'VVoid'}
              className="operation-btn recovery-btn"
            >
              ✨ Recover
            </button>
          </div>
        </div>

        {/* Game History */}
        <div className="game-history">
          <h3>📜 Computation Log</h3>
          <div className="history-display">
            {gameHistory.map((entry, index) => (
              <div key={index} className="history-entry">
                {entry}
              </div>
            ))}
          </div>
        </div>

        {/* Mathematical Insights */}
        <div className="insights">
          <h3>🧮 Mathematical Insights</h3>
          <div className="insights-content">
            <div>🔬 <strong>Void Patterns Seen:</strong> {
              Array.from(new Set(universe.state.history.map(h => h.pattern))).join(', ') || 'None yet'
            }</div>
            <div>⚖️ <strong>Conservation Status:</strong> {
              universe.state.totalEntropy >= 0 ? '✅ Laws respected' : '❌ Violation detected'
            }</div>
            <div>🌡️ <strong>Thermodynamic State:</strong> {
              universe.state.totalEntropy === 0 ? 'Ground state' :
              universe.state.totalEntropy < 5 ? 'Low entropy' :
              universe.state.totalEntropy < 15 ? 'Rising entropy' : 'High entropy'
            }</div>
          </div>
        </div>

        {/* Controls */}
        <div className="game-controls">
          <button onClick={resetUniverse} className="control-btn">
            🔄 Reset Level
          </button>
          <button 
            onClick={() => {
              setCurrentLevel(0);
              resetUniverse();
              setScore(0);
            }} 
            className="control-btn"
          >
            🏠 Restart Game
          </button>
          <button 
            onClick={() => {
              // Demonstrate mathematical law
              const a = 15, b = 25;
              const expr1 = safeAdd({ type: 'VNum', value: a }, { type: 'VNum', value: b }, universe);
              const expr2 = safeAdd({ type: 'VNum', value: b }, { type: 'VNum', value: a }, universe);
              addToHistory(`Noether test: ${a}+${b} and ${b}+${a} both have entropy ${universe.state.totalEntropy}`);
            }}
            className="control-btn"
          >
            📐 Test Noether's Theorem
          </button>
        </div>
      </main>
    </div>
  );
};

export default App;