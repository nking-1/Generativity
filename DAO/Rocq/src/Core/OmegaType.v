(* OmegaType.v: a type where every proposition has a witness. *)
(* We wrap the type so we can analyze its properties using contexts,
   which avoids trivializing the entire framework. *)

Class OmegaType := {
  Omegacarrier : Type;
  omega_completeness : forall (P : Omegacarrier -> Prop), 
    exists x : Omegacarrier, P x
}.