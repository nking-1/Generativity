(** * AlphaType: The Consistent but Incomplete Type
    
    AlphaType represents a type with exactly one impossible predicate,
    differentiating it from OmegaType and NomegaType, which behave like
    maximally paradoxical infinities.
*)

Class AlphaType := {
  Alphacarrier : Type;
  
  (** The unique impossible predicate, bundled with its properties:
      1. It has no witnesses
      2. Any other impossible predicate is equivalent to it *)
  alpha_impossibility : { P : Alphacarrier -> Prop | 
    (forall x : Alphacarrier, ~ P x) /\
    (forall Q : Alphacarrier -> Prop, 
      (forall x : Alphacarrier, ~ Q x) -> 
      (forall x : Alphacarrier, Q x <-> P x))
  };
  
  (** Non-emptiness - need at least one element *)
  alpha_not_empty : exists x : Alphacarrier, True
}.

(** Helper to extract the impossible predicate *)
Definition omega_veil {Alpha : AlphaType} : Alphacarrier -> Prop :=
  proj1_sig (@alpha_impossibility Alpha).
