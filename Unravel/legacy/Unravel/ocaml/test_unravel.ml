(* test_unravel.ml *)
#use "unravel.ml";;  (* Include the extracted code *)

(* Helper to print values *)
let string_of_value = function
  | VNum n -> Printf.sprintf "Num(%d)" n
  | VBool b -> Printf.sprintf "Bool(%b)" b
  | VVoid -> "Void"

let string_of_valueT = function
  | VTNum n -> Printf.sprintf "TNum(%d)" n
  | VTBool b -> Printf.sprintf "TBool(%b)" b
  | VTVoid info -> 
      match info with
      | VInfo (entropy, time, _) -> 
          Printf.sprintf "TVoid(entropy=%d, time=%d)" entropy time

let () =
  Printf.printf "=== Unravel Language Tests ===\n\n";
  
  (* Basic arithmetic *)
  Printf.printf "Simple: 2 + 3 = %s\n" 
    (string_of_value test_simple);
  
  (* Void propagation *)
  Printf.printf "Void propagation: (10/0) + 5 = %s\n" 
    (string_of_value test_void);
  
  (* Recovery *)
  Printf.printf "Recovery: default(10/0, 42) = %s\n" 
    (string_of_value test_recovery);
  
  (* Variables *)
  Printf.printf "Let binding: let x = 10 in x + 5 = %s\n" 
    (string_of_value test_let);
  
  (* Thermodynamics *)
  let (tval, universe) = test_thermo in
  Printf.printf "\n=== Thermodynamic Evaluation ===\n";
  Printf.printf "Value: %s\n" (string_of_valueT tval);
  Printf.printf "Universe state:\n";
  Printf.printf "  Total entropy: %d\n" universe.total_entropy;
  Printf.printf "  Time step: %d\n" universe.time_step;
  Printf.printf "  Void count: %d\n" universe.void_count;
  Printf.printf "  Heat death?: %b\n" (is_heat_death universe);
  
  (* Chaos generator entropy *)
  Printf.printf "\n=== Entropy Growth ===\n";
  for i = 0 to 10 do
    let entropy = get_entropy (chaos_generator i) in
    Printf.printf "chaos(%d) → entropy = %d\n" i entropy
  done;
  
  (* Example evaluations *)
  Printf.printf "\n=== Example Programs ===\n";
  
  let safe_div_ex = eval_default (safe_div 10 0) in
  Printf.printf "safe_div(10, 0) = %s\n" (string_of_value safe_div_ex);
  
  let calc = eval_default calculation in
  Printf.printf "calculation = %s\n" (string_of_value calc);
  
  let risky = eval_default risky_calculation in  
  Printf.printf "risky_calculation = %s\n" (string_of_value risky);
  
  let recovered_val = eval_default recovered in
  Printf.printf "recovered = %s\n" (string_of_value recovered_val)