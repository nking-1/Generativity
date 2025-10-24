(* MinimalAlphaType.v: A simpler construction showing AlphaType's
   sigma type axiom of alpha_impossibility, which asserts pointwise
   equivalence, can be a theorem from an even weaker axiom.
   We use sigma type in AlphaType for practicality. *)

Class MinimalAlphaType := {
  Minalphacarrier : Type;
  alpha_impossible_exists : exists P : Minalphacarrier -> Prop, 
                           forall x, ~ P x;
  alpha_not_empty : exists x : Minalphacarrier, True
}.

Section MinimalProperties.
  Context `{MinimalAlphaType}.
  
  Theorem all_impossible_predicates_pointwise_equal :
    forall P Q : Minalphacarrier -> Prop,
    (forall x, ~P x) -> (forall x, ~Q x) ->
    forall x, P x <-> Q x.
  Proof.
    intros P Q HP HQ x.
    split; intro H'.
    - exfalso. exact (HP x H').
    - exfalso. exact (HQ x H').
  Qed.
  
  (* The limitation of MinimalAlphaType: we cannot extract a specific
     canonical impossible predicate from bare existence *)
  Lemma cannot_name_omega_veil :
    exists P : Minalphacarrier -> Prop, forall x, ~ P x
    (* But cannot define: omega_veil : Minalphacarrier -> Prop *).
  Proof.
    exact alpha_impossible_exists.
  Qed.
  
  (* This is why AlphaType uses a sigma type - it provides both existence
     AND a canonical witness (omega_veil = proj1_sig alpha_impossibility) 
     that can be referenced throughout the framework. *)
  
End MinimalProperties.