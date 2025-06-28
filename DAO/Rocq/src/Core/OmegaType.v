(** * OmegaType: The Complete but Paradoxical Type
    
    OmegaType represents a type where EVERY predicate has a witness.
    This includes contradictory predicates, making it complete but trivial.
*)

Require Import Setoid.

(** ** Definition of OmegaType *)

Class OmegaType := {
  Omegacarrier : Type;
  omega_completeness : forall (P : Omegacarrier -> Prop), 
    exists x : Omegacarrier, P x
}.