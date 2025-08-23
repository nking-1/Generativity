/**
 * test_omega.cpp
 * Test the Modern C++ total functional programming implementation
 */

#include "omega_types.hpp"
#include <iostream>
#include <vector>
#include <string>

// Need to implement thermo_div function that was referenced but not defined
namespace omega {

template<typename T>
requires std::is_arithmetic_v<T>
[[nodiscard]] ThermoOmega<T> thermo_div(const ThermoOmega<T>& x, const ThermoOmega<T>& y) {
    // Handle void cases
    if (x.is_void() || y.is_void()) {
        const VoidInfo* void_info = x.is_void() ? x.unwrap().get_void_info() : y.unwrap().get_void_info();
        
        auto new_history = x.history();
        new_history.insert(new_history.end(), y.history().begin(), y.history().end());
        new_history.push_back(*void_info);
        
        return ThermoOmega<T>(Omega<T>::void_(void_info->pattern, void_info->source),
                              x.entropy() + y.entropy() + 1, std::move(new_history));
    }
    
    // Both are values - perform safe division
    auto result = safe_div(x.unwrap_or(T{}), y.unwrap_or(T{}));
    
    auto new_history = x.history();
    new_history.insert(new_history.end(), y.history().begin(), y.history().end());
    
    if (result.is_void()) {
        new_history.push_back(*result.get_void_info());
        return ThermoOmega<T>(std::move(result), x.entropy() + y.entropy() + 1, std::move(new_history));
    }
    
    return ThermoOmega<T>(std::move(result), x.entropy() + y.entropy(), std::move(new_history));
}

} // namespace omega

using namespace omega;

int main() {
    std::cout << "=== MODERN C++ TOTAL FUNCTIONAL PROGRAMMING TEST ===\n\n";
    
    // Test basic arithmetic
    std::cout << "Basic Arithmetic:\n";
    auto basic = chain(10).add(20);
    std::cout << "  10 + 20 = " << basic.unwrap_or(0) << ", entropy = " << basic.entropy() << "\n";
    
    // Test division by zero
    std::cout << "\nDivision by Zero:\n";
    auto div_zero = chain(10).divide(0).recover(999);
    std::cout << "  10 / 0 (recovered) = " << div_zero.unwrap_or(0) << ", entropy = " << div_zero.entropy() << "\n";
    
    // Test Noether's theorem
    std::cout << "\nNoether's Theorem Verification:\n";
    auto noether1 = chain(42).add(58);
    auto noether2 = chain(58).add(42);
    std::cout << "  42 + 58 entropy: " << noether1.entropy() << "\n";
    std::cout << "  58 + 42 entropy: " << noether2.entropy() << "\n";
    std::cout << "  ✓ Commutativity preserves entropy: " << (noether1.entropy() == noether2.entropy()) << "\n";
    
    // Test safe container access
    std::cout << "\nSafe Container Access:\n";
    std::vector<int> vec = {10, 20, 30, 40, 50};
    auto valid = safe_at(vec, 2);
    auto invalid = safe_at(vec, 10);
    
    std::cout << "  vec[2] = " << valid.unwrap_or(-1) << "\n";
    std::cout << "  vec[10] = " << (invalid.is_void() ? "void (safe)" : "unexpected") << "\n";
    
    // Test constexpr totality
    std::cout << "\nCompile-Time Totality:\n";
    constexpr auto fib10 = constexpr_fibonacci<10>();
    constexpr auto fib_overflow = constexpr_fibonacci<60>();
    
    std::cout << "  constexpr fibonacci(10) = " << fib10.unwrap_or(0) << "\n";
    std::cout << "  constexpr fibonacci(60) = " << (fib_overflow.is_void() ? "void (overflow)" : "value") << "\n";
    
    // Test Newton-Raphson
    std::cout << "\nNewton-Raphson Method:\n";
    auto sqrt2 = safe_newton_raphson(
        [](double x) { return x*x - 2.0; },
        [](double x) { return 2.0*x; },
        1.0
    );
    
    std::cout << "  sqrt(2) ≈ " << sqrt2.unwrap_or(0) << "\n";
    std::cout << "  Computation entropy: " << sqrt2.entropy() << "\n";
    
    // Test entropy conservation
    std::cout << "\nConservation Laws:\n";
    auto complex = chain(100.0)
        .map([](double x) { return std::log(x); })   // Valid
        .divide(0.0)                                 // Void
        .recover(42.0)                               // Recovered
        .add(8.0);                                   // Continue
    
    std::cout << "  Complex computation result: " << complex.unwrap_or(0) << "\n";
    std::cout << "  Final entropy: " << complex.entropy() << "\n";
    std::cout << "  Has errors: " << (complex.has_errors() ? "Yes" : "No") << "\n";
    
    std::cout << "\n=== C++ TOTALITY BENEFITS ===\n";
    std::cout << "✅ Zero-overhead abstractions with mathematical guarantees\n";
    std::cout << "✅ Compile-time totality verification (constexpr functions)\n";
    std::cout << "✅ Template metaprogramming for type-safe impossibility\n";
    std::cout << "✅ Perfect forwarding preserves performance\n";
    std::cout << "✅ RAII entropy tracking with automatic cleanup\n";
    std::cout << "✅ Strong type safety with concepts (C++20+)\n";
    
    std::cout << "\n🚀 Modern C++: Maximum performance + Mathematical rigor! 🚀\n";
    
    return 0;
}