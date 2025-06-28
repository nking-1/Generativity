Require Import DAO.Core.NomegaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.OmegaProperties.

(** ** Properties of NomegaType *)

Section NomegaProperties.
  Context {Nomega : NomegaType}.
  
  (** Helper: The predicate "there exists no x" *)
  Definition no_witness (P : Nomegacarrier -> Prop) : Prop :=
    ~ exists x : Nomegacarrier, P x.
  
  (** For any predicate on Nomega, there are no witnesses *)
  Theorem nomega_no_witnesses : 
    exists P : Nomegacarrier -> Prop, no_witness P.
  Proof.
    exists (fun _ => True).
    unfold no_witness.
    intros [x _].
    exact (nomega_emptiness x).
  Qed.

  (** From any element of Nomega, we can prove anything (ex falso) *)
  Theorem nomega_proves_anything : 
    forall (P : Nomegacarrier -> Prop),
    forall x : Nomegacarrier, P x.
  Proof.
    intros P x.
    (* We have x : Nomegacarrier *)
    (* By nomega_emptiness, this gives us False *)
    destruct (nomega_emptiness x).
    (* From False, we can prove anything - principle of explosion *)
  Qed.

  (** This means we can prove both P and ~P for any element *)
  Theorem nomega_contradiction :
    forall (P : Nomegacarrier -> Prop),
    forall x : Nomegacarrier, P x /\ ~ P x.
  Proof.
    intros P x.
    split.
    - exact (nomega_proves_anything P x).
    - exact (nomega_proves_anything (fun x => ~ P x) x).
  Qed.

  (** In any trivial type, everything equals everything *)
  Definition trivial_equality {T : Type} (contradiction : T -> False) : 
    forall (x y : T), x = y.
  Proof.
    intros x y.
    destruct (contradiction x).
  Qed.
  
  (** All elements of Nomega are equal (vacuously true) *)
  Theorem nomega_all_equal :
    forall (x y : Nomegacarrier), x = y.
  Proof.
    exact (trivial_equality nomega_emptiness).
  Qed.

    (* Both types allow us to prove anything *)
    Theorem omega_nomega_equivalence :
    forall {O : OmegaType} {N : NomegaType},
    (* Both can prove any proposition about their carriers *)
    (forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x) /\
    (forall (Q : Nomegacarrier -> Prop) (y : Nomegacarrier), Q y).
  Proof.
    split.
    - (* Omega case: we have P x and ~P x *)
      intros P x.
      destruct (omega_has_paradoxes P) as [w [Hw Hnw]].
      (* We have Hw : P w and Hnw : ~ P w, which is a contradiction *)
      (* Apply Hnw to Hw to get False *)
      contradiction.
    - (* Nomega case: from any y we get False *)
      intros Q y.
      destruct (nomega_emptiness y).
  Qed.

End NomegaProperties.