use crate::{thermo, omega::{Omega, ThermoOmega}};

/// Simplified real-world examples using only available ThermoOmega methods

#[cfg(test)]
mod financial_calculations {
    use super::*;
    
    /// Portfolio value calculation that never panics
    pub fn calculate_portfolio_value(positions: &[(f64, f64)]) -> ThermoOmega<i32> {
        let mut total = thermo!(0);
        
        for (quantity, price) in positions {
            // Convert to cents to avoid floating point issues
            let quantity_cents = (*quantity * 100.0) as i32;
            let price_cents = (*price * 100.0) as i32;
            
            // This could overflow with large positions
            let position_value = thermo!(quantity_cents)
                .mul(thermo!(price_cents))
                .divide(thermo!(100)); // Back to dollars as cents
            
            total = total.add(position_value);
        }
        
        total.recover(0) // Never fail, always return something
    }
    
    #[test]
    fn test_portfolio_calculation() {
        let positions = vec![
            (100.0, 150.50),  // 100 shares at $150.50
            (50.0, 2800.75),  // 50 shares at $2800.75  
            (25.0, 800.25),   // 25 shares at $800.25
        ];
        
        let result = calculate_portfolio_value(&positions);
        
        println!("Portfolio value: ${:.2}", result.value.unwrap_or(0) as f64 / 100.0);
        println!("Calculation health: {} potential issues", result.entropy);
        
        // We always get a result, never a panic
        assert!(!result.is_void());
    }
    
    #[test]
    fn test_extreme_portfolio() {
        // Test with values that could cause overflow
        let extreme_positions = vec![
            (100000.0, 1000.0),    // Large position
            (50000.0, 2000.0),     // Another large position
        ];
        
        let result = calculate_portfolio_value(&extreme_positions);
        
        println!("Extreme portfolio: ${:.2}", result.value.unwrap_or(0) as f64 / 100.0);
        println!("Entropy from overflows: {}", result.entropy);
        
        // Even with extreme values, we get a result
        // Entropy tells us if calculations overflowed
        if result.entropy > 0 {
            println!("⚠️  Some calculations overflowed - result may be inaccurate");
        }
    }
}

#[cfg(test)]
mod data_processing {
    use super::*;
    
    /// Process sensor data with corruption handling
    pub fn process_sensor_batch(readings: &[Option<i32>]) -> ThermoOmega<i32> {
        let mut sum = thermo!(0);
        let mut valid_count = thermo!(0);
        
        for reading in readings {
            match reading {
                Some(value) => {
                    sum = sum.add(thermo!(*value));
                    valid_count = valid_count.add(thermo!(1));
                }
                None => {
                    // Corrupted reading - add entropy to track the issue
                    sum = sum.add(thermo!(0).divide(thermo!(0)).recover(0));
                }
            }
        }
        
        // Calculate average
        sum.divide(valid_count).recover(0)
    }
    
    #[test]
    fn test_sensor_processing() {
        let readings = vec![
            Some(25),
            Some(27),
            None,        // Corrupted
            Some(23),
            Some(26),
            None,        // Corrupted
        ];
        
        let average = process_sensor_batch(&readings);
        
        println!("Average reading: {}°C", average.value.unwrap_or(0));
        println!("Corrupted readings: {}", average.entropy);
        
        // We get an average AND know how many readings were corrupted
        assert!(!average.is_void());
        assert_eq!(average.entropy, 2); // Two corrupted readings
        
        // The average is (25+27+23+26)/4 = 25.25 ≈ 25
        assert_eq!(average.value.unwrap_or(0), 25);
    }
}

#[cfg(test)]
mod system_metrics {
    use super::*;
    
    /// Calculate system load with error tracking
    pub fn calculate_cpu_load_average(samples: &[i32]) -> ThermoOmega<i32> {
        let mut total = thermo!(0);
        let mut count = thermo!(0);
        
        for &sample in samples {
            if sample >= 0 && sample <= 100 {
                // Valid CPU percentage
                total = total.add(thermo!(sample));
                count = count.add(thermo!(1));
            } else {
                // Invalid reading - add entropy but continue
                total = total.add(thermo!(0).divide(thermo!(0)).recover(0));
            }
        }
        
        total.divide(count).recover(0)
    }
    
    #[test]
    fn test_cpu_load_calculation() {
        let samples = vec![45, 52, -1, 67, 150, 43, 58]; // -1 and 150 are invalid
        
        let avg_load = calculate_cpu_load_average(&samples);
        
        println!("Average CPU load: {}%", avg_load.value.unwrap_or(0));
        println!("Invalid samples: {}", avg_load.entropy);
        
        // We get an average despite invalid data
        assert!(!avg_load.is_void());
        assert_eq!(avg_load.entropy, 2); // Two invalid samples
        
        // Average of valid samples: (45+52+67+43+58)/5 = 53
        assert_eq!(avg_load.value.unwrap_or(0), 53);
    }
}

#[cfg(test)]
mod gaming_damage {
    use super::*;
    
    /// Game damage calculation that never crashes
    pub fn calculate_damage(
        base_damage: i32,
        weapon_multiplier: i32,
        critical_multiplier: i32,
    ) -> ThermoOmega<i32> {
        // Base damage * weapon multiplier
        let weapon_damage = thermo!(base_damage)
            .mul(thermo!(weapon_multiplier));
        
        // Apply critical hit multiplier  
        let final_damage = weapon_damage
            .mul(thermo!(critical_multiplier))
            .divide(thermo!(100)); // Convert back from percentage
        
        // Always do at least 1 damage, never crash the game
        final_damage.recover(1)
    }
    
    #[test]
    fn test_damage_calculation() {
        // Normal damage
        let damage1 = calculate_damage(50, 2, 100); // 50 * 2 * 100% = 100
        println!("Normal damage: {} (entropy: {})", 
                damage1.value.unwrap_or(0), damage1.entropy);
        assert_eq!(damage1.value.unwrap_or(0), 100);
        
        // Critical hit
        let damage2 = calculate_damage(50, 2, 200); // 50 * 2 * 200% = 200
        println!("Critical damage: {} (entropy: {})", 
                damage2.value.unwrap_or(0), damage2.entropy);
        assert_eq!(damage2.value.unwrap_or(0), 200);
        
        // Extreme values that could overflow
        let damage3 = calculate_damage(i32::MAX / 2, 10, 300);
        println!("Extreme damage: {} (entropy: {})", 
                damage3.value.unwrap_or(0), damage3.entropy);
        
        // Game never crashes, always gets some damage value
        assert!(!damage3.is_void());
        if damage3.entropy > 0 {
            println!("⚠️  Damage calculation overflowed - using fallback");
        }
    }
}

#[cfg(test)]
mod configuration_parsing {
    use super::*;
    
    #[derive(Debug)]
    pub struct ServerConfig {
        pub port: i32,
        pub max_connections: i32,
        pub timeout_seconds: i32,
        pub config_entropy: u32, // Track configuration issues
    }
    
    /// Parse server configuration with fallbacks
    pub fn parse_server_config(
        port_str: Option<&str>,
        max_conn_str: Option<&str>,
        timeout_str: Option<&str>,
    ) -> ServerConfig {
        // Parse port with validation
        let port = port_str
            .and_then(|s| s.parse::<i32>().ok())
            .filter(|&p| p > 0 && p < 65536)
            .map(|p| thermo!(p))
            .unwrap_or_else(|| {
                // Invalid port - use default but add entropy
                thermo!(8080).add(thermo!(0).divide(thermo!(0)).recover(0))
            });
        
        // Parse max connections
        let max_conn = max_conn_str
            .and_then(|s| s.parse::<i32>().ok())
            .filter(|&c| c > 0)
            .map(|c| thermo!(c))
            .unwrap_or_else(|| thermo!(100));
        
        // Parse timeout
        let timeout = timeout_str
            .and_then(|s| s.parse::<i32>().ok())
            .filter(|&t| t > 0)
            .map(|t| thermo!(t))
            .unwrap_or_else(|| {
                // Invalid timeout - use default but add entropy
                thermo!(30).add(thermo!(0).divide(thermo!(0)).recover(0))
            });
        
        ServerConfig {
            port: port.value.unwrap_or(8080),
            max_connections: max_conn.value.unwrap_or(100),
            timeout_seconds: timeout.value.unwrap_or(30),
            config_entropy: port.entropy + max_conn.entropy + timeout.entropy,
        }
    }
    
    #[test]
    fn test_config_parsing() {
        // Valid configuration
        let config1 = parse_server_config(
            Some("3000"),
            Some("200"), 
            Some("60")
        );
        println!("Valid config: {:?}", config1);
        assert_eq!(config1.config_entropy, 0);
        assert_eq!(config1.port, 3000);
        
        // Invalid configuration
        let config2 = parse_server_config(
            Some("invalid"),  // Bad port
            Some("-50"),      // Negative connections  
            Some("0")         // Zero timeout
        );
        println!("Invalid config: {:?}", config2);
        
        // Application starts with defaults, but we know config was bad
        assert!(config2.config_entropy > 0);
        assert_eq!(config2.port, 8080);           // Default
        assert_eq!(config2.max_connections, 100); // Default
        assert_eq!(config2.timeout_seconds, 30);  // Default
        
        println!("🔧 Config had {} issues but application started safely", 
                 config2.config_entropy);
    }
}

// Key benefits demonstrated:
// 
// 1. **Never Crash**: All calculations return results even on overflow
// 2. **Error Tracking**: Entropy tells us what went wrong
// 3. **Graceful Fallbacks**: Use defaults but track the issues  
// 4. **Production Safety**: Systems stay online despite bad data
// 5. **Observability**: Entropy becomes a valuable health metric
// 6. **Audit Trails**: Know exactly how many issues occurred