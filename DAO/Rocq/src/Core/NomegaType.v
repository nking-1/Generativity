(** * NomegaType.v
    NomegaType represents a type with no elements - the empty type.
    In the DAO framework, it represents Wu (無) - nothingness/void.
    In regular type theory, this is like the bottom type.
*)

Class NomegaType := {
  Nomegacarrier : Type;
  nomega_emptiness : forall x : Nomegacarrier, False
}.
