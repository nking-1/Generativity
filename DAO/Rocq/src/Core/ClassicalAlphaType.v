(* ClassicalAlphaType.v *)
Class ClassicalAlphaType := {
    Alphacarrier : Type;

    (* The unique impossible predicate - using pointwise equivalence *)
    alpha_impossibility : {P: Alphacarrier -> Prop | 
    (forall x: Alphacarrier, ~ P x) /\
    (forall Q: Alphacarrier -> Prop, 
        (forall x: Alphacarrier, ~ Q x) -> 
        (forall x: Alphacarrier, Q x <-> P x))};

    (* Non-emptiness *)
    alpha_not_empty : exists x: Alphacarrier, True;

    (* In this formulation, we explicitly axiomatize classical logic for propositions - this is excluded middle *)
    alpha_constant_decision : forall P : Prop, P \/ ~ P
}.

(* Omega veil for the ClassicalAlphaType - named classical_veil to avoid conflict *)
Definition classical_veil `{H_N: ClassicalAlphaType} : Alphacarrier -> Prop :=
 proj1_sig alpha_impossibility.
