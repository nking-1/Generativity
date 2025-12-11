(** * VoidType.v
    VoidType represents a type with no elements - the empty type.
    In the DAO framework, it represents Wu (無) - nothingness/void.
    In regular type theory, this is like the bottom type.
*)

Class VoidType := {
  Voidcarrier : Type;
  void_emptiness : forall x : Voidcarrier, False
}.
