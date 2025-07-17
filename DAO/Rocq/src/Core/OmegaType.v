(* OmegaType: a type where every proposition has a witness. *)

Class OmegaType := {
  Omegacarrier : Type;
  omega_completeness : forall (P : Omegacarrier -> Prop), 
    exists x : Omegacarrier, P x
}.