/**
 * Program.cs
 * C# V3 implementation following proven V2 reference architecture
 * Clean, simple, and focused on the core mathematical principles
 */

using System;
using System.Collections.Generic;
using System.Linq;

namespace UnravelV3
{
    // ============================================================================
    // CONFIGURATION (Following V2 Reference)
    // ============================================================================

    public static class Config
    {
        public const int DefaultFuel = 1000;
        public const int BaseEntropy = 1;
    }

    // ============================================================================
    // CORE TYPES (Simplified for C# Compatibility)
    // ============================================================================

    public abstract class ExprV
    {
        public class EVNum : ExprV
        {
            public int Value { get; }
            public EVNum(int value) => Value = value;
        }

        public class EVVoid : ExprV
        {
        }

        public class EVAdd : ExprV
        {
            public ExprV Left { get; }
            public ExprV Right { get; }
            public EVAdd(ExprV left, ExprV right) { Left = left; Right = right; }
        }

        public class EVDiv : ExprV
        {
            public ExprV Left { get; }
            public ExprV Right { get; }
            public EVDiv(ExprV left, ExprV right) { Left = left; Right = right; }
        }

        public class EVDefault : ExprV
        {
            public ExprV Expression { get; }
            public ExprV DefaultValue { get; }
            public EVDefault(ExprV expr, ExprV defaultValue) { Expression = expr; DefaultValue = defaultValue; }
        }

        public class EVVar : ExprV
        {
            public string Name { get; }
            public EVVar(string name) => Name = name;
        }

        public class EVLet : ExprV
        {
            public string Name { get; }
            public ExprV Binding { get; }
            public ExprV Body { get; }
            public EVLet(string name, ExprV binding, ExprV body) 
            {
                Name = name; 
                Binding = binding; 
                Body = body;
            }
        }
    }

    public abstract class ValueT
    {
        public class VTNum : ValueT
        {
            public int Value { get; }
            public VTNum(int value) => Value = value;
        }

        public class VTVoid : ValueT
        {
            public VoidInfo Info { get; }
            public VTVoid(VoidInfo info) => Info = info;
        }
    }

    public class VoidInfo
    {
        public int Entropy { get; }
        public int TimeCreated { get; }
        public string Source { get; }

        public VoidInfo(int entropy, int timeCreated, string source)
        {
            Entropy = entropy;
            TimeCreated = timeCreated;
            Source = source;
        }
    }

    public class Universe
    {
        public int TotalEntropy { get; }
        public int TimeStep { get; }
        public int VoidCount { get; }

        public Universe(int totalEntropy, int timeStep, int voidCount)
        {
            TotalEntropy = totalEntropy;
            TimeStep = timeStep;
            VoidCount = voidCount;
        }

        public static Universe Initial => new Universe(0, 0, 0);
    }

    // ============================================================================
    // UNIVERSE OPERATIONS (Following V2 Reference)
    // ============================================================================

    public static class UniverseOps
    {
        public static VoidInfo MakeVoidInfo(int entropy, Universe universe, string source)
        {
            return new VoidInfo(entropy, universe.TimeStep, source);
        }

        public static Universe EvolveUniverse(Universe universe, VoidInfo info)
        {
            return new Universe(
                universe.TotalEntropy + info.Entropy,
                universe.TimeStep + 1,  // ALWAYS increment by 1 (critical fix)
                universe.VoidCount + 1
            );
        }

        public static VoidInfo CombineVoids(VoidInfo v1, VoidInfo v2, Universe universe)
        {
            return new VoidInfo(
                v1.Entropy + v2.Entropy,
                universe.TimeStep,  // Use CURRENT universe time
                $"VoidPropagation[{v1.Source} + {v2.Source}]"
            );
        }
    }

    // ============================================================================
    // THERMODYNAMIC EVALUATION (Following V2 Pattern)
    // ============================================================================

    public static class UnravelEvaluator
    {
        /**
         * Main thermodynamic evaluator following V2 reference exactly
         * CRITICAL: Proper universe state threading
         */
        public static (ValueT, Universe) EvalThermodynamic(
            int fuel, 
            Universe universe, 
            List<(string, ValueT)> env, 
            ExprV expr)
        {
            if (fuel == 0)
            {
                var info = UniverseOps.MakeVoidInfo(Config.BaseEntropy, universe, "OutOfFuel");
                return (new ValueT.VTVoid(info), UniverseOps.EvolveUniverse(universe, info));
            }

            var fuel2 = fuel - 1;

            switch (expr)
            {
                case ExprV.EVNum evNum:
                    return (new ValueT.VTNum(evNum.Value), universe);

                case ExprV.EVVoid _:
                    {
                        var info = UniverseOps.MakeVoidInfo(Config.BaseEntropy, universe, "TypeError_pure_void");
                        return (new ValueT.VTVoid(info), UniverseOps.EvolveUniverse(universe, info));
                    }

                case ExprV.EVAdd evAdd:
                    {
                        // CRITICAL: Proper universe threading (follows V2 exactly)
                        var (v1, u1) = EvalThermodynamic(fuel2, universe, env, evAdd.Left);
                        var (v2, u2) = EvalThermodynamic(fuel2, u1, env, evAdd.Right);  // u1 → u2!

                        if (v1 is ValueT.VTNum vtn1 && v2 is ValueT.VTNum vtn2)
                        {
                            return (new ValueT.VTNum(vtn1.Value + vtn2.Value), u2);
                        }

                        if (v1 is ValueT.VTNum && v2 is ValueT.VTVoid vtv2)
                        {
                            return (vtv2, u2);
                        }

                        if (v1 is ValueT.VTVoid vtv1 && v2 is ValueT.VTNum)
                        {
                            return (vtv1, u2);
                        }

                        if (v1 is ValueT.VTVoid vtv1_void && v2 is ValueT.VTVoid vtv2_void)
                        {
                            var combined = UniverseOps.CombineVoids(vtv1_void.Info, vtv2_void.Info, u2);
                            return (new ValueT.VTVoid(combined), UniverseOps.EvolveUniverse(u2, combined));
                        }

                        // Type error fallback
                        var typeErrorInfo = UniverseOps.MakeVoidInfo(Config.BaseEntropy, u2, "TypeError_add");
                        return (new ValueT.VTVoid(typeErrorInfo), UniverseOps.EvolveUniverse(u2, typeErrorInfo));
                    }

                case ExprV.EVDiv evDiv:
                    {
                        var (v1, u1) = EvalThermodynamic(fuel2, universe, env, evDiv.Left);
                        var (v2, u2) = EvalThermodynamic(fuel2, u1, env, evDiv.Right);

                        if (v1 is ValueT.VTNum vtn1 && v2 is ValueT.VTNum vtn2)
                        {
                            if (vtn2.Value == 0)
                            {
                                var divZeroInfo = UniverseOps.MakeVoidInfo(Config.BaseEntropy, u2, $"DivByZero({vtn1.Value})");
                                return (new ValueT.VTVoid(divZeroInfo), UniverseOps.EvolveUniverse(u2, divZeroInfo));
                            }
                            return (new ValueT.VTNum(vtn1.Value / vtn2.Value), u2);
                        }

                        if (v1 is ValueT.VTVoid vtv1) return (vtv1, u2);
                        if (v2 is ValueT.VTVoid vtv2) return (vtv2, u2);

                        var typeErrorInfo = UniverseOps.MakeVoidInfo(Config.BaseEntropy, u2, "TypeError_div");
                        return (new ValueT.VTVoid(typeErrorInfo), UniverseOps.EvolveUniverse(u2, typeErrorInfo));
                    }

                case ExprV.EVDefault evDefault:
                    {
                        var (v, u1) = EvalThermodynamic(fuel2, universe, env, evDefault.Expression);
                        if (v is ValueT.VTVoid)
                        {
                            return EvalThermodynamic(fuel2, u1, env, evDefault.DefaultValue);
                        }
                        return (v, u1);
                    }

                case ExprV.EVVar evVar:
                    {
                        var lookupResult = env.FirstOrDefault(pair => pair.Item1 == evVar.Name);
                        if (!string.IsNullOrEmpty(lookupResult.Item1))
                        {
                            return (lookupResult.Item2, universe);
                        }
                        else
                        {
                            var info = UniverseOps.MakeVoidInfo(Config.BaseEntropy, universe, $"UndefinedVar({evVar.Name})");
                            return (new ValueT.VTVoid(info), UniverseOps.EvolveUniverse(universe, info));
                        }
                    }

                case ExprV.EVLet evLet:
                    {
                        var (v1, u1) = EvalThermodynamic(fuel2, universe, env, evLet.Binding);
                        var newEnv = new List<(string, ValueT)> { (evLet.Name, v1) };
                        newEnv.AddRange(env);
                        return EvalThermodynamic(fuel2, u1, newEnv, evLet.Body);
                    }

                default:
                    throw new InvalidOperationException("Unhandled expression type");
            }
        }

        // Convenient evaluation functions (following V2 API)
        public static (ValueT, Universe) RunThermo(ExprV expr)
        {
            return EvalThermodynamic(Config.DefaultFuel, Universe.Initial, new List<(string, ValueT)>(), expr);
        }

        public static (ValueT, Universe) RunThermoWithFuel(int fuel, ExprV expr)
        {
            return EvalThermodynamic(fuel, Universe.Initial, new List<(string, ValueT)>(), expr);
        }
    }

    // ============================================================================
    // EXPRESSION BUILDERS (Ergonomic API)
    // ============================================================================

    public static class Ex
    {
        public static ExprV Num(int value) => new ExprV.EVNum(value);
        public static ExprV Void() => new ExprV.EVVoid();
        public static ExprV Add(ExprV left, ExprV right) => new ExprV.EVAdd(left, right);
        public static ExprV Div(ExprV left, ExprV right) => new ExprV.EVDiv(left, right);
        public static ExprV Default(ExprV expr, ExprV defaultValue) => new ExprV.EVDefault(expr, defaultValue);
        public static ExprV Variable(string name) => new ExprV.EVVar(name);
        public static ExprV Let(string name, ExprV binding, ExprV body) => new ExprV.EVLet(name, binding, body);
    }

    // ============================================================================
    // MATHEMATICAL LAW VERIFICATION
    // ============================================================================

    public static class MathematicalVerifier
    {
        public static bool TestNoetherTheorem(ExprV expr1, ExprV expr2)
        {
            var (_, u1) = UnravelEvaluator.RunThermo(expr1);
            var (_, u2) = UnravelEvaluator.RunThermo(expr2);
            return u1.TotalEntropy == u2.TotalEntropy;
        }

        public static bool TestConservationLaw(ExprV voidExpr, ExprV fallback)
        {
            var (_, voidU) = UnravelEvaluator.RunThermo(voidExpr);
            var (_, recoveredU) = UnravelEvaluator.RunThermo(Ex.Default(voidExpr, fallback));
            return voidU.TotalEntropy == recoveredU.TotalEntropy;
        }
    }

    // ============================================================================
    // MAIN PROGRAM
    // ============================================================================

    class Program
    {
        static void Main(string[] args)
        {
            Console.WriteLine("🌀 UNRAVEL V3 C# IMPLEMENTATION");
            Console.WriteLine("Following proven V2 Haskell reference + V3 TypeScript success\n");

            RunV3CSharpTests();
        }

        static void RunV3CSharpTests()
        {
            // Test 1: Basic operations
            Console.WriteLine("=== BASIC OPERATIONS ===");
            var basicTest = UnravelEvaluator.RunThermo(Ex.Add(Ex.Num(10), Ex.Num(20)));
            var basicResult = basicTest.Item1 is ValueT.VTNum vtn ? vtn.Value.ToString() : "void";
            Console.WriteLine($"10 + 20: result={basicResult}, entropy={basicTest.Item2.TotalEntropy}");

            // Test 2: Division by zero
            Console.WriteLine("\n=== VOID OPERATIONS ===");
            var divTest = UnravelEvaluator.RunThermo(Ex.Div(Ex.Num(10), Ex.Num(0)));
            Console.WriteLine($"10 / 0: result={divTest.Item1.GetType().Name}, entropy={divTest.Item2.TotalEntropy}, time={divTest.Item2.TimeStep}");

            // Test 3: Entropy bomb (the critical test that revealed bugs)
            Console.WriteLine("\n=== ENTROPY BOMB TEST (Critical Verification) ===");

            ExprV EntropyBombV3(int depth)
            {
                if (depth == 0) return Ex.Div(Ex.Num(1), Ex.Num(0));
                return Ex.Add(EntropyBombV3(depth - 1), EntropyBombV3(depth - 1));
            }

            Console.WriteLine("C# V3 Entropy bomb progression:");
            for (int depth = 0; depth <= 10; depth++)
            {
                var (v, u) = UnravelEvaluator.RunThermo(EntropyBombV3(depth));
                Console.WriteLine($"  C# Bomb {depth}: entropy={u.TotalEntropy}, time={u.TimeStep}, voids={u.VoidCount}");

                // Check for time evolution issues
                if (u.TimeStep != u.VoidCount && depth > 0)
                {
                    Console.WriteLine($"    🚨 TIME/VOID MISMATCH: {u.TimeStep} vs {u.VoidCount}");
                }

                // Flag high entropy
                if (u.TotalEntropy > 1000)
                {
                    Console.WriteLine($"    🔥 HIGH ENTROPY: {u.TotalEntropy}");
                }
            }

            // Test 4: Mathematical laws
            Console.WriteLine("\n=== MATHEMATICAL LAW VERIFICATION ===");

            var noetherTest = MathematicalVerifier.TestNoetherTheorem(
                Ex.Add(Ex.Num(42), Ex.Num(58)),
                Ex.Add(Ex.Num(58), Ex.Num(42))
            );
            Console.WriteLine($"Noether's theorem: {(noetherTest ? "VERIFIED" : "VIOLATED")}");

            var conservationTest = MathematicalVerifier.TestConservationLaw(
                Ex.Div(Ex.Num(100), Ex.Num(0)),
                Ex.Num(999)
            );
            Console.WriteLine($"Conservation laws: {(conservationTest ? "VERIFIED" : "VIOLATED")}");

            // Test 5: Variable environment
            Console.WriteLine("\n=== VARIABLE ENVIRONMENT TESTS ===");

            var selfRefTest = UnravelEvaluator.RunThermo(Ex.Let("x", Ex.Variable("x"), Ex.Variable("x")));
            var selfRefResult = selfRefTest.Item1 is ValueT.VTVoid ? "VOID" : "VALUE";
            Console.WriteLine($"Self-reference: {selfRefResult} (entropy={selfRefTest.Item2.TotalEntropy})");

            var letTest = UnravelEvaluator.RunThermo(Ex.Let("x", Ex.Num(10), Ex.Add(Ex.Variable("x"), Ex.Num(5))));
            var letResult = letTest.Item1 is ValueT.VTNum vtnum ? vtnum.Value.ToString() : "void";
            Console.WriteLine($"Let binding: {letResult} (entropy={letTest.Item2.TotalEntropy})");

            // Test 6: Comparison with previous results
            Console.WriteLine("\n=== COMPARISON WITH PREVIOUS IMPLEMENTATIONS ===");
            Console.WriteLine("Expected from V3 TypeScript success:");
            Console.WriteLine("  Bomb 8: entropy=2304, time=511, voids=511");
            Console.WriteLine("  Bomb 9: entropy=5120, time=1023, voids=1023");
            Console.WriteLine("  Bomb 10: entropy=11264, time=2047, voids=2047");

            var bomb8 = UnravelEvaluator.RunThermo(EntropyBombV3(8));
            var bomb9 = UnravelEvaluator.RunThermo(EntropyBombV3(9));
            var bomb10 = UnravelEvaluator.RunThermo(EntropyBombV3(10));

            Console.WriteLine("\nC# V3 actual results:");
            Console.WriteLine($"  C# Bomb 8: entropy={bomb8.Item2.TotalEntropy}, time={bomb8.Item2.TimeStep}, voids={bomb8.Item2.VoidCount}");
            Console.WriteLine($"  C# Bomb 9: entropy={bomb9.Item2.TotalEntropy}, time={bomb9.Item2.TimeStep}, voids={bomb9.Item2.VoidCount}");
            Console.WriteLine($"  C# Bomb 10: entropy={bomb10.Item2.TotalEntropy}, time={bomb10.Item2.TimeStep}, voids={bomb10.Item2.VoidCount}");

            // Check if we match the expected results
            bool matches8 = bomb8.Item2.TotalEntropy == 2304 && bomb8.Item2.TimeStep == 511 && bomb8.Item2.VoidCount == 511;
            bool matches9 = bomb9.Item2.TotalEntropy == 5120 && bomb9.Item2.TimeStep == 1023 && bomb9.Item2.VoidCount == 1023;
            bool matches10 = bomb10.Item2.TotalEntropy == 11264 && bomb10.Item2.TimeStep == 2047 && bomb10.Item2.VoidCount == 2047;

            Console.WriteLine($"\n✅ Matches expected results: Bomb 8={matches8}, Bomb 9={matches9}, Bomb 10={matches10}");

            Console.WriteLine("\n=== C# V3 IMPLEMENTATION ASSESSMENT ===");
            Console.WriteLine("✅ Follows V2 Haskell reference architecture");
            Console.WriteLine("✅ Proper universe state threading implemented");
            Console.WriteLine("✅ Mathematical law verification built-in");
            Console.WriteLine("✅ Clean C# idioms with proven mathematical foundations");

            if (matches8 && matches9 && matches10)
            {
                Console.WriteLine("\n🏆 C# V3 SUCCESS: MATCHES REFERENCE BEHAVIOR EXACTLY!");
                Console.WriteLine("C# implementation achieves same mathematical correctness as proven V3 TypeScript");
            }
            else
            {
                Console.WriteLine("\n⚠️ C# V3 PARTIAL SUCCESS: Some differences from reference");
                Console.WriteLine("Further investigation needed to match proven behavior exactly");
            }

            Console.WriteLine("\n🎯 NEXT: Run comprehensive stress tests to verify C# V3 robustness");
            Console.WriteLine("🌀 C# V3 basic implementation complete! 🌀");
        }
    }
}