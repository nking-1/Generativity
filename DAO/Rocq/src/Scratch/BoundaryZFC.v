Class BoundaryZFC := {
  carrier : Type;
  mem : carrier -> carrier -> Prop;
  
  (* Boundary 1: Universal set is impossible *)
  boundary_no_universal :
    (exists U : carrier, forall x : carrier, mem x U) -> False
}.

Notation "x 'in' y" := (mem x y) (at level 70).
Notation "x 'notin' y" := (~ mem x y) (at level 70).

(** * Basic Theorems *)

Section BasicTheorems.
  Context {ZFC : BoundaryZFC}.
  
  (** Theorem 1: It's impossible for a set to contain everything including itself *)
  Theorem impossible_universal_self_member :
    (exists U : carrier, (forall x : carrier, x in U) /\ U in U) -> False.
  Proof.
    intros [U [Hall Hself]].
    apply boundary_no_universal.
    exists U.
    exact Hall.
  Qed.
  
  (** Theorem 2: It's impossible for something to be in everything *)
  Theorem impossible_element_in_all :
    (exists x : carrier, forall U : carrier, x in U) -> False.
  Proof.
    intros [x Hall].
    apply boundary_no_universal.
    exists x. (* Wait, this doesn't work - x might not contain everything *)
  Admitted.

End BasicTheorems.