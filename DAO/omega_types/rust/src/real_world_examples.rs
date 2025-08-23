use crate::{thermo, omega::{Omega, ThermoOmega}};

/// Real-world software engineering scenarios where omega_types provides significant value

#[cfg(test)]
mod financial_systems {
    use super::*;
    
    /// Financial calculations that CANNOT crash but need error tracking
    pub fn calculate_portfolio_value(
        positions: &[(String, f64, f64)], // (symbol, quantity, price)
        exchange_rates: &[f64],
    ) -> ThermoOmega<i64> {
        let mut total_value = thermo!(0_i64);
        
        for (i, (symbol, quantity, price)) in positions.iter().enumerate() {
            // Convert to cents to avoid floating point issues
            let quantity_cents = (*quantity * 100.0) as i32;
            let price_cents = (*price * 100.0) as i32;
            
            // Calculate position value - could overflow with large positions
            let position_value = thermo!(quantity_cents)
                .mul(thermo!(price_cents))
                .divide(thermo!(100)); // Back to cents
            
            // Apply exchange rate if available
            let final_value = if i < exchange_rates.len() {
                let rate_basis = (exchange_rates[i] * 10000.0) as i32;
                position_value
                    .mul(thermo!(rate_basis))
                    .divide(thermo!(10000))
            } else {
                // Missing exchange rate - use 1.0 but adds entropy
                position_value.add(thermo!(0).divide(thermo!(0)).recover(0))
            };
            
            total_value = total_value.add(final_value);
        }
        
        total_value.recover(0) // Never fail, but track all errors
    }
    
    #[test]
    fn test_portfolio_calculation() {
        let positions = vec![
            ("AAPL".to_string(), 100.0, 150.50),
            ("GOOGL".to_string(), 50.0, 2800.75),
            ("TSLA".to_string(), 25.0, 800.25),
        ];
        
        // Missing exchange rates for last position
        let exchange_rates = vec![1.0, 0.85]; // Missing rate for TSLA
        
        let result = calculate_portfolio_value(&positions, &exchange_rates);
        
        println!("Portfolio value: ${:.2}", result.value.unwrap_or(0) as f64 / 100.0);
        println!("Computational health: {} errors", result.entropy);
        
        // We got a result AND know something went wrong (missing exchange rate)
        assert!(!result.is_void());
        assert!(result.entropy > 0, "Should track missing exchange rate as error");
    }
}

#[cfg(test)]
mod data_processing_pipelines {
    use super::*;
    
    /// ETL pipeline that processes data with potential corruption
    pub fn process_sensor_readings(readings: &[Option<i32>]) -> ThermoOmega<i32> {
        let mut sum = thermo!(0);
        let mut count = thermo!(0);
        
        for reading in readings {
            match reading {
                Some(value) => {
                    // Valid reading - could still overflow in sum
                    sum = sum.add(thermo!(*value));
                    count = count.add(thermo!(1));
                }
                None => {
                    // Corrupted reading - add entropy but continue processing
                    sum = sum.add(thermo!(0).divide(thermo!(0)).recover(0));
                    // Don't count corrupted readings
                }
            }
        }
        
        // Calculate average, handling division by zero if all readings corrupted
        sum.divide(count).recover(0)
    }
    
    #[test]
    fn test_sensor_processing() {
        let readings = vec![
            Some(25),
            Some(27),
            None,        // Corrupted
            Some(23),
            None,        // Corrupted  
            Some(26),
        ];
        
        let avg = process_sensor_readings(&readings);
        
        println!("Average reading: {}°C", avg.value.unwrap_or(0));
        println!("Data quality: {} corrupted readings", avg.entropy);
        
        // We got an average (25.25°C) AND know 2 readings were corrupted
        assert_eq!(avg.value.unwrap_or(0), 25); // (25+27+23+26)/4 ≈ 25
        assert_eq!(avg.entropy, 2); // Two corrupted readings
    }
}

#[cfg(test)]
mod gaming_systems {
    use super::*;
    
    /// Game damage calculation that never crashes the game
    pub fn calculate_combat_damage(
        base_damage: i32,
        weapon_multiplier: i32, 
        critical_chance: i32,  // 0-100
        armor_value: i32,
    ) -> ThermoOmega<i32> {
        // Critical hit calculation
        let is_critical = critical_chance > 75; // Simplified for demo
        let crit_multiplier = if is_critical { thermo!(200) } else { thermo!(100) };
        
        // Base damage with weapon multiplier - could overflow
        let raw_damage = thermo!(base_damage)
            .mul(thermo!(weapon_multiplier))
            .mul(crit_multiplier)
            .divide(thermo!(100)); // Convert percentage back
        
        // Apply armor reduction - armor could be negative (debuff) causing issues
        let armor_reduction = thermo!(100)
            .sub(thermo!(armor_value.min(95))); // Cap armor at 95% reduction
        
        raw_damage
            .mul(armor_reduction)
            .divide(thermo!(100))
            .recover(1) // Always do at least 1 damage, never crash the game
    }
    
    #[test] 
    fn test_damage_calculation() {
        // Normal case
        let damage1 = calculate_combat_damage(50, 3, 80, 25);
        println!("Normal damage: {} (entropy: {})", damage1.value.unwrap_or(0), damage1.entropy);
        
        // Edge case: extreme values that could overflow
        let damage2 = calculate_combat_damage(i32::MAX/2, 10, 95, -50);
        println!("Extreme damage: {} (entropy: {})", damage2.value.unwrap_or(0), damage2.entropy);
        
        // The game never crashes, we always get some damage value
        assert!(!damage1.is_void());
        assert!(!damage2.is_void());
    }
}

#[cfg(test)]
mod api_services {
    use super::*;
    
    /// Rate limiting service that tracks degradation
    pub fn check_rate_limit(
        user_id: u32,
        current_requests: i32,
        rate_limit: i32,
        time_window_seconds: i32,
    ) -> ThermoOmega<i32> {
        // Calculate requests per second - avoid division by zero
        let rps = thermo!(current_requests)
            .divide(thermo!(time_window_seconds.max(1)));
        
        // Calculate remaining quota - convert to Omega for subtraction
        let remaining = match (thermo!(rate_limit).value, rps.value) {
            (crate::omega::Omega::Value(limit), crate::omega::Omega::Value(used)) => {
                let diff = crate::omega::Omega::new(limit) - crate::omega::Omega::new(used);
                ThermoOmega {
                    value: diff,
                    entropy: rps.entropy,
                }
            }
            _ => ThermoOmega::void_with_entropy(rps.entropy + 1),
        };
        
        // If over limit, return 0 remaining but track the violation
        if remaining.is_void() {
            // Rate limit exceeded - add entropy to track violation  
            thermo!(0).add(thermo!(1).divide(thermo!(0)).recover(0))
        } else {
            remaining
        }.recover(0)
    }
    
    #[test]
    fn test_rate_limiting() {
        // Normal usage
        let quota1 = check_rate_limit(123, 45, 100, 60);
        println!("User quota: {} req/s remaining (violations: {})", 
                quota1.value.unwrap_or(0), quota1.entropy);
        
        // Exceeded rate limit
        let quota2 = check_rate_limit(456, 150, 100, 60);
        println!("User quota: {} req/s remaining (violations: {})", 
                quota2.value.unwrap_or(0), quota2.entropy);
        
        // Invalid time window
        let quota3 = check_rate_limit(789, 50, 100, 0);
        println!("User quota: {} req/s remaining (issues: {})", 
                quota3.value.unwrap_or(0), quota3.entropy);
        
        // API never returns 500 error, always gives some response
        // Entropy tells us about violations and system health
        assert_eq!(quota2.entropy, 1); // One rate limit violation
    }
}

#[cfg(test)]
mod configuration_systems {
    use super::*;
    
    /// Configuration parser that uses defaults but tracks issues
    #[derive(Debug)]
    pub struct DatabaseConfig {
        pub pool_size: i32,
        pub timeout_ms: i32,
        pub retry_count: i32,
        pub entropy: u32, // Track config issues
    }
    
    pub fn parse_database_config(
        pool_size_str: Option<&str>,
        timeout_str: Option<&str>, 
        retry_str: Option<&str>,
    ) -> DatabaseConfig {
        // Parse pool size with fallback
        let pool_size = pool_size_str
            .and_then(|s| s.parse::<i32>().ok())
            .map(|v| thermo!(v))
            .unwrap_or_else(|| {
                // Invalid config - use default but add entropy
                thermo!(10).add(thermo!(1).divide(thermo!(0)).recover(0))
            });
        
        // Parse timeout with validation
        let timeout = timeout_str
            .and_then(|s| s.parse::<i32>().ok())
            .map(|v| if v > 0 { thermo!(v) } else { 
                // Invalid timeout - use default but add entropy
                thermo!(5000).add(thermo!(1).divide(thermo!(0)).recover(0))
            })
            .unwrap_or_else(|| thermo!(5000));
        
        // Parse retry count with bounds
        let retry = retry_str
            .and_then(|s| s.parse::<i32>().ok())
            .map(|v| thermo!(v.clamp(1, 10))) // Reasonable bounds
            .unwrap_or_else(|| thermo!(3));
        
        // Combine all entropy
        let total_entropy = pool_size.entropy + timeout.entropy + retry.entropy;
        
        DatabaseConfig {
            pool_size: pool_size.value.unwrap_or(10),
            timeout_ms: timeout.value.unwrap_or(5000),
            retry_count: retry.value.unwrap_or(3),
            entropy: total_entropy,
        }
    }
    
    #[test]
    fn test_config_parsing() {
        // Valid config
        let config1 = parse_database_config(
            Some("20"),
            Some("3000"), 
            Some("5")
        );
        println!("Config 1: {:?}", config1);
        assert_eq!(config1.entropy, 0);
        
        // Invalid config values
        let config2 = parse_database_config(
            Some("not_a_number"),
            Some("-100"),  // Invalid negative timeout
            None          // Missing retry config
        );
        println!("Config 2: {:?}", config2);
        
        // App still starts with defaults, but we know config had issues
        assert!(config2.entropy > 0);
        assert_eq!(config2.pool_size, 10);    // Default
        assert_eq!(config2.timeout_ms, 5000); // Default due to invalid
        assert_eq!(config2.retry_count, 3);   // Default due to missing
    }
}

#[cfg(test)]
mod monitoring_systems {
    use super::*;
    
    /// System health metrics where entropy becomes a first-class metric
    pub fn calculate_system_health_score(
        cpu_percent: i32,      // 0-100
        memory_percent: i32,   // 0-100
        disk_percent: i32,     // 0-100
        error_rate: i32,       // errors per minute
    ) -> ThermoOmega<i32> {
        // Healthy baseline
        let mut health = thermo!(100);
        
        // CPU penalty - could overflow with extreme values
        let cpu_penalty = thermo!(cpu_percent)
            .sub(thermo!(80))
            .or(thermo!(0)); // Only penalize if > 80%
        
        // Memory penalty 
        let memory_penalty = thermo!(memory_percent)
            .sub(thermo!(85))
            .or(thermo!(0));
        
        // Disk penalty
        let disk_penalty = thermo!(disk_percent)
            .sub(thermo!(90))
            .or(thermo!(0));
        
        // Error rate penalty - errors add entropy AND reduce score
        let error_penalty = thermo!(error_rate)
            .mul(thermo!(2)); // Each error costs 2 points
        
        // Add artificial entropy for each error (errors are "computational disorder")
        let error_entropy = (0..error_rate.min(100)).fold(thermo!(0), |acc, _| {
            acc.add(thermo!(1).divide(thermo!(0)).recover(0))
        });
        
        health
            .sub(cpu_penalty)
            .sub(memory_penalty) 
            .sub(disk_penalty)
            .sub(error_penalty)
            .add(error_entropy) // Adds entropy without changing value
            .or(thermo!(0)) // Never negative
            .recover(0)
    }
    
    #[test]
    fn test_system_health() {
        // Healthy system
        let health1 = calculate_system_health_score(45, 60, 70, 0);
        println!("Healthy system: {}% (entropy: {})", 
                health1.value.unwrap_or(0), health1.entropy);
        
        // Stressed system with errors
        let health2 = calculate_system_health_score(95, 90, 85, 5);
        println!("Stressed system: {}% (entropy: {})", 
                health2.value.unwrap_or(0), health2.entropy);
        
        // The entropy becomes a valuable metric itself!
        // High entropy = system is experiencing many errors/issues
        assert_eq!(health1.entropy, 0);  // No errors = no entropy
        assert!(health2.entropy > 0);    // Errors = entropy increase
    }
}

// Summary of real-world value propositions:
// 
// 1. **Never Crash**: Production systems that cannot afford panics
// 2. **Graceful Degradation**: Continue operating with partial failures  
// 3. **Error Tracking**: Know what went wrong even after recovery
// 4. **Health Metrics**: Entropy as a first-class observability metric
// 5. **Audit Trails**: Track computational reliability for compliance
// 6. **Resilient Pipelines**: Process as much data as possible
// 7. **Configuration Safety**: Use defaults but track invalid config
// 8. **Rate Limiting**: Track violations without failing requests
// 9. **Financial Safety**: Never lose money due to calculation panics
// 10. **Gaming**: Never crash the game, always produce some result