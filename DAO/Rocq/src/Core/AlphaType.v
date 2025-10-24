(** AlphaType.v: The Consistent but Incomplete Type
    AlphaType represents a type with at least one impossible predicate
*)

Class AlphaType := {
  Alphacarrier : Type;
  
  (** An impossible predicate:
      1. It has no witnesses
      2. Any other impossible predicate is pointwise equivalent to it
      Alpha makes no assumptions about intensional vs extensional equality
      of impossible predicates, but both options are explored in other files. *)
  alpha_impossibility : { P : Alphacarrier -> Prop | 
    (forall x : Alphacarrier, ~ P x) /\
    (forall Q : Alphacarrier -> Prop, 
      (forall x : Alphacarrier, ~ Q x) -> 
      (forall x : Alphacarrier, Q x <-> P x))
  };

  (** Non-emptiness - need at least one element *)
  alpha_not_empty : { x : Alphacarrier | True }
}.

(* Returns the P : Alphacarrier -> Prop from the dependent pair 
   We call it omega_veil because it is one of the contradictions that
   has been ruled out from OmegaType, but can still be expressed as a false
   predicate in AlphaType. *)
Definition omega_veil {Alpha : AlphaType} : Alphacarrier -> Prop :=
  proj1_sig (@alpha_impossibility Alpha).

