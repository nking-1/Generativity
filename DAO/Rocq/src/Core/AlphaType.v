(** AlphaType.v: The Consistent but Incomplete Type
    AlphaType represents a type with at least one impossible predicate.
    Certain truths are "veiled" from Omega in order to create space for
    coherent existence in an AlphaType.
*)

Class AlphaType := {
  Alphacarrier : Type;
  
  (** An impossible predicate:
      1. It has no witnesses
      2. Any other impossible predicate is pointwise equivalent to it
      3. There may be more than one impossible predicate for an AlphaType
      4. Alphacarrier's inhabitants exist within the space of possibility left over
      5. Impossible predicates are pointwise equal to False, but intensionally & syntactically distinct *)
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

