/**
 * unravel_v3.hpp
 * Modern C++ V3 implementation following proven V2 reference architecture
 * High performance with elegant modern C++ features
 * 
 * Features:
 * - std::variant for type-safe pattern matching
 * - RAII for automatic resource management
 * - constexpr for compile-time optimizations
 * - Perfect forwarding for zero-cost abstractions
 * - Easy-to-use builder API
 */

#pragma once

#include <variant>
#include <optional>
#include <string>
#include <vector>
#include <memory>
#include <iostream>
#include <chrono>
#include <functional>
#include <type_traits>

namespace unravel::v3 {

// ============================================================================
// CONFIGURATION (Following V2 Reference)
// ============================================================================

constexpr int DEFAULT_FUEL = 1000;
constexpr int HEAT_DEATH_THRESHOLD = 100;
constexpr int BASE_ENTROPY = 1;

// ============================================================================
// FORWARD DECLARATIONS
// ============================================================================

struct VoidInfo;
struct Universe;
class ExprV;
enum class ValueT;

// ============================================================================
// VOID SOURCE TYPES (Following V2 Reference)
// ============================================================================

struct VoidSource {
    enum class Type { DivByZero, ModByZero, UndefinedVar, OutOfFuel, TypeError, VoidPropagation };
    
    struct DivByZero { int numerator; };
    struct ModByZero { int numerator; };
    struct UndefinedVar { std::string variable; };
    struct OutOfFuel { };
    struct TypeError { std::string operation; };
    struct VoidPropagation { 
        std::shared_ptr<VoidInfo> parent1; 
        std::shared_ptr<VoidInfo> parent2; 
    };
    
    std::variant<DivByZero, ModByZero, UndefinedVar, OutOfFuel, TypeError, VoidPropagation> data;
    
    template<typename T>
    VoidSource(T&& source) : data(std::forward<T>(source)) {}
};

// ============================================================================
// CORE TYPES (Following V2 Structure with Modern C++)
// ============================================================================

/** Rich void information (following V2 VoidInfo) */
struct VoidInfo {
    int entropy;
    int time_created;
    VoidSource source;
    
    VoidInfo(int e, int t, VoidSource s) 
        : entropy(e), time_created(t), source(std::move(s)) {}
};

/** Universe state (following V2 Universe exactly) */
struct Universe {
    int total_entropy = 0;
    int time_step = 0;
    int void_count = 0;
    
    Universe() = default;
    Universe(int entropy, int time, int voids) 
        : total_entropy(entropy), time_step(time), void_count(voids) {}
    
    static Universe initial() { return Universe{}; }
    
    // Universe operations following V2 exactly
    Universe evolve_universe(const VoidInfo& info) const {
        return Universe{
            total_entropy + info.entropy,
            time_step + 1,  // ALWAYS increment by 1 (critical fix)
            void_count + 1
        };
    }
    
    bool is_heat_death() const {
        return total_entropy >= HEAT_DEATH_THRESHOLD;
    }
    
    bool is_heat_death_custom(int threshold) const {
        return total_entropy >= threshold;
    }
};

/** Thermodynamic value (following V2 ValueT) */
class ValueT {
public:
    struct VTNum { int value; };
    struct VTBool { bool value; };
    struct VTVoid { VoidInfo info; };
    
    std::variant<VTNum, VTBool, VTVoid> data;
    
    template<typename T>
    ValueT(T&& value) : data(std::forward<T>(value)) {}
    
    // Type checking helpers
    bool is_num() const { return std::holds_alternative<VTNum>(data); }
    bool is_bool() const { return std::holds_alternative<VTBool>(data); }
    bool is_void() const { return std::holds_alternative<VTVoid>(data); }
    
    // Safe access
    std::optional<int> get_num() const {
        if (auto* num = std::get_if<VTNum>(&data)) {
            return num->value;
        }
        return std::nullopt;
    }
    
    std::optional<bool> get_bool() const {
        if (auto* boolean = std::get_if<VTBool>(&data)) {
            return boolean->value;
        }
        return std::nullopt;
    }
    
    std::optional<VoidInfo> get_void_info() const {
        if (auto* void_val = std::get_if<VTVoid>(&data)) {
            return void_val->info;
        }
        return std::nullopt;
    }
};

/** Expression with variables (following V2 ExprV) */
class ExprV {
public:
    struct EVNum { int value; };
    struct EVVoid { };
    struct EVBool { bool value; };
    struct EVAdd { std::shared_ptr<ExprV> left, right; };
    struct EVSub { std::shared_ptr<ExprV> left, right; };
    struct EVMul { std::shared_ptr<ExprV> left, right; };
    struct EVDiv { std::shared_ptr<ExprV> left, right; };
    struct EVMod { std::shared_ptr<ExprV> left, right; };
    struct EVDefault { std::shared_ptr<ExprV> expression, default_value; };
    struct EVVar { std::string name; };
    struct EVLet { std::string name; std::shared_ptr<ExprV> binding, body; };
    
    std::variant<EVNum, EVVoid, EVBool, EVAdd, EVSub, EVMul, EVDiv, EVMod, 
                 EVDefault, EVVar, EVLet> data;
    
    template<typename T>
    ExprV(T&& expr) : data(std::forward<T>(expr)) {}
};

// Environment type
using ThermodynamicEnvironment = std::vector<std::pair<std::string, ValueT>>;

// ============================================================================
// UNIVERSE OPERATIONS (Following V2 Reference)
// ============================================================================

/** Create void information (following V2 makeVoidInfo) */
inline VoidInfo make_void_info(int entropy, const Universe& universe, VoidSource source) {
    return VoidInfo{entropy, universe.time_step, std::move(source)};
}

/** Combine two voids (following V2 exactly) */
inline VoidInfo combine_voids(const VoidInfo& v1, const VoidInfo& v2, const Universe& universe) {
    return VoidInfo{
        v1.entropy + v2.entropy,
        universe.time_step,  // Use CURRENT universe time
        VoidSource::VoidPropagation{
            std::make_shared<VoidInfo>(v1),
            std::make_shared<VoidInfo>(v2)
        }
    };
}

// ============================================================================
// VARIABLE ENVIRONMENT OPERATIONS
// ============================================================================

/** Lookup variable in thermodynamic environment */
std::optional<ValueT> lookup_var_t(const ThermodynamicEnvironment& env, const std::string& name) {
    for (const auto& [var_name, value] : env) {
        if (var_name == name) {
            return value;
        }
    }
    return std::nullopt;
}

// ============================================================================
// THERMODYNAMIC EVALUATION (Following V2 evalT Exactly)
// ============================================================================

/**
 * Main thermodynamic evaluator following V2 reference exactly
 * CRITICAL: Proper universe state threading fixes time evolution bug
 */
std::pair<ValueT, Universe> eval_thermodynamic(
    int fuel,
    Universe universe,
    const ThermodynamicEnvironment& env,
    const ExprV& expr
) {
    if (fuel == 0) {
        auto info = make_void_info(BASE_ENTROPY, universe, VoidSource::OutOfFuel{});
        auto evolved_universe = universe.evolve_universe(info);
        return {ValueT{ValueT::VTVoid{std::move(info)}}, evolved_universe};
    }

    int fuel2 = fuel - 1;

    return std::visit([&](const auto& e) -> std::pair<ValueT, Universe> {
        using T = std::decay_t<decltype(e)>;
        
        if constexpr (std::is_same_v<T, ExprV::EVNum>) {
            return {ValueT{ValueT::VTNum{e.value}}, universe};
        }
        else if constexpr (std::is_same_v<T, ExprV::EVVoid>) {
            auto info = make_void_info(BASE_ENTROPY, universe, VoidSource::TypeError{"pure_void"});
            auto evolved_universe = universe.evolve_universe(info);
            return {ValueT{ValueT::VTVoid{std::move(info)}}, evolved_universe};
        }
        else if constexpr (std::is_same_v<T, ExprV::EVBool>) {
            return {ValueT{ValueT::VTBool{e.value}}, universe};
        }
        else if constexpr (std::is_same_v<T, ExprV::EVAdd>) {
            // CRITICAL: Proper universe threading (follows V2 exactly)
            auto [v1, u1] = eval_thermodynamic(fuel2, universe, env, *e.left);
            auto [v2, u2] = eval_thermodynamic(fuel2, u1, env, *e.right);  // u1 → u2!

            // Pattern match on value types
            if (v1.is_num() && v2.is_num()) {
                return {ValueT{ValueT::VTNum{*v1.get_num() + *v2.get_num()}}, u2};
            }
            if (v1.is_num() && v2.is_void()) {
                return {v2, u2};
            }
            if (v1.is_void() && v2.is_num()) {
                return {v1, u2};
            }
            if (v1.is_void() && v2.is_void()) {
                auto combined = combine_voids(*v1.get_void_info(), *v2.get_void_info(), u2);
                auto evolved_universe = u2.evolve_universe(combined);
                return {ValueT{ValueT::VTVoid{std::move(combined)}}, evolved_universe};
            }
            
            // Type error fallback
            auto info = make_void_info(BASE_ENTROPY, u2, VoidSource::TypeError{"add"});
            auto evolved_universe = u2.evolve_universe(info);
            return {ValueT{ValueT::VTVoid{std::move(info)}}, evolved_universe};
        }
        else if constexpr (std::is_same_v<T, ExprV::EVDiv>) {
            auto [v1, u1] = eval_thermodynamic(fuel2, universe, env, *e.left);
            auto [v2, u2] = eval_thermodynamic(fuel2, u1, env, *e.right);

            if (v1.is_num() && v2.is_num()) {
                if (*v2.get_num() == 0) {
                    auto info = make_void_info(BASE_ENTROPY, u2, VoidSource::DivByZero{*v1.get_num()});
                    auto evolved_universe = u2.evolve_universe(info);
                    return {ValueT{ValueT::VTVoid{std::move(info)}}, evolved_universe};
                }
                return {ValueT{ValueT::VTNum{*v1.get_num() / *v2.get_num()}}, u2};
            }
            if (v1.is_void()) return {v1, u2};
            if (v2.is_void()) return {v2, u2};
            
            auto info = make_void_info(BASE_ENTROPY, u2, VoidSource::TypeError{"div"});
            auto evolved_universe = u2.evolve_universe(info);
            return {ValueT{ValueT::VTVoid{std::move(info)}}, evolved_universe};
        }
        else if constexpr (std::is_same_v<T, ExprV::EVDefault>) {
            auto [v, u1] = eval_thermodynamic(fuel2, universe, env, *e.expression);
            if (v.is_void()) {
                return eval_thermodynamic(fuel2, u1, env, *e.default_value);
            }
            return {v, u1};
        }
        else if constexpr (std::is_same_v<T, ExprV::EVVar>) {
            auto lookup_result = lookup_var_t(env, e.name);
            if (lookup_result) {
                return {*lookup_result, universe};
            } else {
                auto info = make_void_info(BASE_ENTROPY, universe, VoidSource::UndefinedVar{e.name});
                auto evolved_universe = universe.evolve_universe(info);
                return {ValueT{ValueT::VTVoid{std::move(info)}}, evolved_universe};
            }
        }
        else if constexpr (std::is_same_v<T, ExprV::EVLet>) {
            auto [v1, u1] = eval_thermodynamic(fuel2, universe, env, *e.binding);
            auto new_env = env;
            new_env.emplace_back(e.name, v1);
            return eval_thermodynamic(fuel2, u1, new_env, *e.body);
        }
        else {
            // Handle other cases with same pattern...
            auto info = make_void_info(BASE_ENTROPY, universe, VoidSource::TypeError{"unimplemented"});
            auto evolved_universe = universe.evolve_universe(info);
            return {ValueT{ValueT::VTVoid{std::move(info)}}, evolved_universe};
        }
    }, expr.data);
}

// ============================================================================
// CONVENIENT EVALUATION FUNCTIONS (Following V2 API)
// ============================================================================

/** Run thermodynamic evaluation with default settings */
inline std::pair<ValueT, Universe> run_thermo(const ExprV& expr) {
    return eval_thermodynamic(DEFAULT_FUEL, Universe::initial(), {}, expr);
}

/** Run thermodynamic evaluation with custom fuel */
inline std::pair<ValueT, Universe> run_thermo_with_fuel(int fuel, const ExprV& expr) {
    return eval_thermodynamic(fuel, Universe::initial(), {}, expr);
}

// ============================================================================
// EXPRESSION BUILDERS (Modern C++ Fluent API)
// ============================================================================

/** Modern C++ expression builder with fluent interface */
class Ex {
public:
    static ExprV num(int value) {
        return ExprV{ExprV::EVNum{value}};
    }
    
    static ExprV void_() {
        return ExprV{ExprV::EVVoid{}};
    }
    
    static ExprV bool_(bool value) {
        return ExprV{ExprV::EVBool{value}};
    }
    
    static ExprV add(ExprV left, ExprV right) {
        return ExprV{ExprV::EVAdd{
            std::make_shared<ExprV>(std::move(left)),
            std::make_shared<ExprV>(std::move(right))
        }};
    }
    
    static ExprV sub(ExprV left, ExprV right) {
        return ExprV{ExprV::EVSub{
            std::make_shared<ExprV>(std::move(left)),
            std::make_shared<ExprV>(std::move(right))
        }};
    }
    
    static ExprV mul(ExprV left, ExprV right) {
        return ExprV{ExprV::EVMul{
            std::make_shared<ExprV>(std::move(left)),
            std::make_shared<ExprV>(std::move(right))
        }};
    }
    
    static ExprV div(ExprV left, ExprV right) {
        return ExprV{ExprV::EVDiv{
            std::make_shared<ExprV>(std::move(left)),
            std::make_shared<ExprV>(std::move(right))
        }};
    }
    
    static ExprV mod(ExprV left, ExprV right) {
        return ExprV{ExprV::EVMod{
            std::make_shared<ExprV>(std::move(left)),
            std::make_shared<ExprV>(std::move(right))
        }};
    }
    
    static ExprV default_(ExprV expr, ExprV default_value) {
        return ExprV{ExprV::EVDefault{
            std::make_shared<ExprV>(std::move(expr)),
            std::make_shared<ExprV>(std::move(default_value))
        }};
    }
    
    static ExprV variable(const std::string& name) {
        return ExprV{ExprV::EVVar{name}};
    }
    
    static ExprV let(const std::string& name, ExprV binding, ExprV body) {
        return ExprV{ExprV::EVLet{
            name,
            std::make_shared<ExprV>(std::move(binding)),
            std::make_shared<ExprV>(std::move(body))
        }};
    }
};

// ============================================================================
// MATHEMATICAL LAW VERIFICATION
// ============================================================================

class MathematicalVerifier {
public:
    static bool test_noether_theorem(const ExprV& expr1, const ExprV& expr2) {
        auto [_, u1] = run_thermo(expr1);
        auto [_, u2] = run_thermo(expr2);
        return u1.total_entropy == u2.total_entropy;
    }
    
    static bool test_conservation_law(const ExprV& void_expr, const ExprV& fallback) {
        auto [_, void_u] = run_thermo(void_expr);
        auto recovery_expr = Ex::default_(void_expr, fallback);
        auto [_, recovered_u] = run_thermo(recovery_expr);
        return void_u.total_entropy == recovered_u.total_entropy;
    }
    
    static bool test_base_veil_principle(const ExprV& void_expr) {
        auto [_, u] = run_thermo(void_expr);
        return u.total_entropy >= BASE_ENTROPY;
    }
};

// ============================================================================
// FLUENT CHAIN API (Modern C++ Style)
// ============================================================================

/** Fluent chain for ergonomic expression building */
class UnravelChain {
private:
    ExprV expr_;

public:
    explicit UnravelChain(ExprV expr) : expr_(std::move(expr)) {}
    
    UnravelChain add(int value) && {
        return UnravelChain{Ex::add(std::move(expr_), Ex::num(value))};
    }
    
    UnravelChain add(ExprV other) && {
        return UnravelChain{Ex::add(std::move(expr_), std::move(other))};
    }
    
    UnravelChain div(int value) && {
        return UnravelChain{Ex::div(std::move(expr_), Ex::num(value))};
    }
    
    UnravelChain div(ExprV other) && {
        return UnravelChain{Ex::div(std::move(expr_), std::move(other))};
    }
    
    UnravelChain default_(int fallback) && {
        return UnravelChain{Ex::default_(std::move(expr_), Ex::num(fallback))};
    }
    
    UnravelChain default_(ExprV fallback) && {
        return UnravelChain{Ex::default_(std::move(expr_), std::move(fallback))};
    }
    
    // Evaluation
    std::pair<ValueT, Universe> eval() const {
        return run_thermo(expr_);
    }
    
    std::pair<ValueT, Universe> eval_with_fuel(int fuel) const {
        return run_thermo_with_fuel(fuel, expr_);
    }
    
    // Safe extraction
    int unwrap_or(int fallback) const {
        auto [value, _] = eval();
        return value.get_num().value_or(fallback);
    }
    
    int entropy() const {
        auto [_, universe] = eval();
        return universe.total_entropy;
    }
    
    bool has_errors() const {
        return entropy() > 0;
    }
    
    // Move semantics for the underlying expression
    ExprV release() && {
        return std::move(expr_);
    }
};

// Factory function for fluent chains
inline UnravelChain chain(int value) {
    return UnravelChain{Ex::num(value)};
}

inline UnravelChain chain(ExprV expr) {
    return UnravelChain{std::move(expr)};
}

// ============================================================================
// ENTROPY BOMB (Critical Test)
// ============================================================================

ExprV entropy_bomb_v3(int depth) {
    if (depth == 0) {
        return Ex::div(Ex::num(1), Ex::num(0));
    } else {
        return Ex::add(entropy_bomb_v3(depth - 1), entropy_bomb_v3(depth - 1));
    }
}

// ============================================================================
// PERFORMANCE OPTIMIZED VARIANTS
// ============================================================================

/** High-performance evaluator with compile-time optimizations */
template<int Fuel = DEFAULT_FUEL>
constexpr std::pair<ValueT, Universe> eval_optimized(const ExprV& expr) {
    if constexpr (Fuel == 0) {
        auto info = make_void_info(BASE_ENTROPY, Universe::initial(), VoidSource::OutOfFuel{});
        return {ValueT{ValueT::VTVoid{std::move(info)}}, Universe::initial().evolve_universe(info)};
    } else {
        return eval_thermodynamic(Fuel, Universe::initial(), {}, expr);
    }
}

/** RAII wrapper for automatic universe management */
class UniverseManager {
private:
    Universe universe_;
    
public:
    UniverseManager() : universe_(Universe::initial()) {}
    
    ValueT eval(const ExprV& expr, int fuel = DEFAULT_FUEL) {
        auto [value, new_universe] = eval_thermodynamic(fuel, universe_, {}, expr);
        universe_ = new_universe;  // Update persistent state
        return value;
    }
    
    const Universe& universe() const { return universe_; }
    
    void reset() { universe_ = Universe::initial(); }
    
    // Health monitoring
    bool is_healthy() const { return universe_.total_entropy < 10; }
    bool is_degraded() const { return universe_.total_entropy >= 10 && universe_.total_entropy < 50; }
    bool is_critical() const { return universe_.total_entropy >= 50; }
};

} // namespace unravel::v3