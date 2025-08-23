#[cfg(test)]
mod overflow_analysis {
    use crate::omega::Omega;
    
    #[test]
    fn analyze_modulo_overflow() {
        println!("i32::MIN = {}", i32::MIN);
        println!("Testing various modulo operations...");
        
        // This should work
        let safe = i32::MIN % 1;
        println!("i32::MIN % 1 = {}", safe);
        
        // This should work  
        let safe2 = i32::MIN % 2;
        println!("i32::MIN % 2 = {}", safe2);
        
        // This is the problematic case
        println!("About to test i32::MIN % -1...");
        
        // Let's use checked_rem to see what happens
        match i32::MIN.checked_rem(-1) {
            Some(result) => println!("i32::MIN.checked_rem(-1) = Some({})", result),
            None => println!("i32::MIN.checked_rem(-1) = None (overflow!)"),
        }
        
        // Let's also test wrapping_rem
        let wrapped = i32::MIN.wrapping_rem(-1);
        println!("i32::MIN.wrapping_rem(-1) = {}", wrapped);
        
        // And overflowing_rem
        let (result, overflow) = i32::MIN.overflowing_rem(-1);
        println!("i32::MIN.overflowing_rem(-1) = ({}, {})", result, overflow);
        
        // Why does this overflow? Because:
        // i32::MIN / -1 would be 2^31, but max i32 is 2^31 - 1
        // So the division overflows, and remainder can't be computed
        println!("i32::MIN = {}", i32::MIN);
        println!("i32::MAX = {}", i32::MAX);
        println!("i32::MIN / -1 would be: {}, but i32::MAX is {}", 
                 (i32::MIN as i64) / -1, i32::MAX);
    }
    
    #[test]
    fn test_other_overflow_cases() {
        // Are there other cases that could overflow?
        let test_cases = vec![
            (i32::MIN, -1),
            (i32::MIN, 1),
            (i32::MAX, -1),
            (i32::MAX, 1),
            (-1, i32::MIN),
            (1, i32::MIN),
        ];
        
        for (a, b) in test_cases {
            match a.checked_rem(b) {
                Some(result) => println!("{} % {} = {}", a, b, result),
                None => println!("{} % {} = OVERFLOW", a, b),
            }
        }
    }
    
    #[test] 
    fn test_fixed_modulo_operations() {
        // Test the critical case that was panicking
        let critical = Omega::new(i32::MIN) % Omega::new(-1);
        assert!(critical.is_void(), "i32::MIN % -1 should return Void, got {:?}", critical);
        
        // Test the instance method too
        let critical2 = Omega::new(i32::MIN).modulo(-1);
        assert!(critical2.is_void(), "i32::MIN.modulo(-1) should return Void, got {:?}", critical2);
        
        // Test division by zero still works
        let div_zero = Omega::new(10) % Omega::new(0);
        assert!(div_zero.is_void(), "Division by zero should return Void");
        
        // Test normal cases still work
        let normal = Omega::new(10) % Omega::new(3);
        assert_eq!(normal, Omega::Value(1), "Normal modulo should work");
        
        println!("✅ All modulo overflow cases fixed!");
    }
    
    #[test]
    fn test_other_arithmetic_overflow_cases() {
        // Let's test if other operations can overflow too
        println!("Testing other potential overflow scenarios...");
        
        // Addition overflow
        let add_result = Omega::new(i32::MAX) + Omega::new(1);
        println!("i32::MAX + 1 = {:?}", add_result);
        
        // Subtraction underflow
        let sub_result = Omega::new(i32::MIN) - Omega::new(1);
        println!("i32::MIN - 1 = {:?}", sub_result);
        
        // Multiplication overflow
        let mul_result = Omega::new(i32::MAX) * Omega::new(2);
        println!("i32::MAX * 2 = {:?}", mul_result);
        
        // Division - the special case i32::MIN / -1
        match i32::MIN.checked_div(-1) {
            Some(result) => println!("i32::MIN.checked_div(-1) = Some({})", result),
            None => {
                println!("i32::MIN.checked_div(-1) = None (overflow!)");
                // Test our Omega implementation
                let div_result = Omega::new(i32::MIN) / Omega::new(-1);
                println!("Omega: i32::MIN / -1 = {:?}", div_result);
            }
        }
    }
    
    #[test]
    fn comprehensive_overflow_protection_test() {
        println!("Testing comprehensive overflow protection...");
        
        // Test ALL overflow cases to make sure they return Void instead of panic
        let overflow_cases = vec![
            // Addition overflow
            (Omega::new(i32::MAX) + Omega::new(1), "i32::MAX + 1"),
            (Omega::new(i32::MIN) + Omega::new(-1), "i32::MIN + (-1)"),
            
            // Subtraction underflow  
            (Omega::new(i32::MIN) - Omega::new(1), "i32::MIN - 1"),
            (Omega::new(i32::MAX) - Omega::new(-1), "i32::MAX - (-1)"),
            
            // Multiplication overflow
            (Omega::new(i32::MAX) * Omega::new(2), "i32::MAX * 2"),
            (Omega::new(i32::MIN) * Omega::new(-1), "i32::MIN * (-1)"),
            
            // Division overflow
            (Omega::new(i32::MIN) / Omega::new(-1), "i32::MIN / (-1)"),
            
            // Modulo overflow
            (Omega::new(i32::MIN) % Omega::new(-1), "i32::MIN % (-1)"),
        ];
        
        for (result, description) in overflow_cases {
            println!("{}: {:?}", description, result);
            assert!(result.is_void(), "{} should return Void, got {:?}", description, result);
        }
        
        // Test that normal operations still work
        let normal_cases = vec![
            (Omega::new(5) + Omega::new(3), Omega::Value(8), "5 + 3"),
            (Omega::new(10) - Omega::new(4), Omega::Value(6), "10 - 4"),
            (Omega::new(6) * Omega::new(7), Omega::Value(42), "6 * 7"),
            (Omega::new(20) / Omega::new(4), Omega::Value(5), "20 / 4"),
            (Omega::new(17) % Omega::new(5), Omega::Value(2), "17 % 5"),
        ];
        
        for (result, expected, description) in normal_cases {
            println!("{}: {:?}", description, result);
            assert_eq!(result, expected, "{} should work normally", description);
        }
        
        println!("✅ All overflow protection tests passed!");
        println!("✅ Library now truly implements total functions!");
    }
}