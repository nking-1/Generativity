(** * DualUnivalence.v
    ---------------------------------------
    The dual of Voevodsky's Univalence Axiom:
    Impossible predicates collapse uniquely
    to the canonical contradiction ω_veil.

    We prove:

      Is_Impossible(P) <-> (P ≃ omega_veil)

    This is the "Univalence of False":
    all contradictions are equivalent.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import DAO.Theory.Impossibility.ParadoxNumbers.
Import ParadoxNumbers ParadoxNaturals.
Import ImpossibilityAlgebra Core.

From DAO.Theory.Impossibility Require Import PureImpossibilitySymmetry.
Import PureImpossibilitySymmetry.PureImpossibilitySymmetry.

Module DualUnivalence.
  Section OmegaUnivalence.
    Context {Alpha : AlphaType}.

    (** ------------------------------------------------------------ *)
    (** 1. Universe of Impossibility (Ω-Universe)                    *)
    (** ------------------------------------------------------------ *)

    Definition Omega := Alphacarrier -> Prop.

    (** Membership: P ∈ Ω iff P is impossible *)
    Definition is_in_Omega (P : Omega) : Prop :=
      Is_Impossible P.

    (** The canonical point of Ω is omega_veil *)
    Definition omega_point : Omega := omega_veil.


    (** ------------------------------------------------------------ *)
    (** 2. Omega-Equivalence                                         *)
    (** ------------------------------------------------------------ *)

    (** P and Q have the same contradiction content *)
    Definition Omega_equiv (P Q : Omega) : Prop :=
      forall a, P a <-> Q a.

    (** Symmetry, reflexivity, transitivity *)
    Lemma Omega_equiv_refl : forall P, Omega_equiv P P.
    Proof. intro P; intro a; split; tauto. Qed.

    Lemma Omega_equiv_sym : forall P Q,
      Omega_equiv P Q -> Omega_equiv Q P.
    Proof. intros P Q H a; specialize (H a); tauto. Qed.

    Lemma Omega_equiv_trans : forall P Q R,
      Omega_equiv P Q -> Omega_equiv Q R -> Omega_equiv P R.
    Proof.
      intros P Q R H1 H2 a.
      specialize (H1 a); specialize (H2 a); tauto.
    Qed.


    (** ------------------------------------------------------------ *)
    (** 3. Key Lemma: Impossibility is Extensional                   *)
    (** ------------------------------------------------------------ *)

    Lemma impossible_ext :
      forall P Q : Omega,
      Omega_equiv P Q ->
      Is_Impossible P ->
      Is_Impossible Q.
    Proof.
      intros P Q Heq HP a.
      specialize (Heq a).
      destruct (HP a) as [HPtoω HωtoP].
      split.
      - (* Q a -> omega_veil a *)
        intro HQa.
        apply HPtoω.
        apply Heq.
        exact HQa.
      - (* omega_veil a -> Q a *)
        intro Hωa.
        apply Heq.
        apply HωtoP.
        exact Hωa.
    Qed.


    (** ------------------------------------------------------------ *)
    (** 4. Dual Univalence Statement                                 *)
    (** ------------------------------------------------------------ *)

    (** The equivalence type between P and omega_veil *)
    Definition Omega_equiv_to_point (P : Omega) : Prop :=
      Omega_equiv P omega_point.

    (** ★ THE MAIN THEOREM ★  
        Univalence for FALSE / Contradiction
    *)

    Theorem Omega_Univalence :
      forall P : Omega,
        Is_Impossible P <-> Omega_equiv P omega_point.
    Proof.
      intro P.
      split.

      (** → Direction: Impossible predicates collapse to omega_veil *)
      - intro HP.
        unfold Omega_equiv, omega_point.
        intro a.
        specialize (HP a).
        assumption.

      (** ← Direction: If P ≃ ω_veil, then P is impossible *)
      - intro Heq.
        unfold Is_Impossible.
        intro a.
        unfold Omega_equiv, omega_point in Heq.
        specialize (Heq a).
        assumption.
    Qed.


    (** ------------------------------------------------------------ *)
    (** 5. Consequences of Omega-Univalence                          *)
    (** ------------------------------------------------------------ *)

    (** 1. The Ω-universe is contractible *)
    Theorem Omega_contractible :
      forall P Q : Omega,
        is_in_Omega P ->
        is_in_Omega Q ->
        Omega_equiv P Q.
    Proof.
      intros P Q HP HQ.
      apply Omega_equiv_trans with (Q := omega_veil).
      - apply (proj1 (Omega_Univalence P)); exact HP.
      - apply Omega_equiv_sym.
        apply (proj1 (Omega_Univalence Q)); exact HQ.
    Qed.

    (** 2. All contradictions have the same paradox-depth *)
    Section OmegaSameDepth.
      Context (dec :
        forall P : Alphacarrier -> Prop,
          {Is_Impossible P} + {~ Is_Impossible P}).

      Let Omega := Alphacarrier -> Prop.

      Theorem Omega_same_depth :
        forall P : Omega,
          Is_Impossible P ->
          pure_predicate_action dec P = POne.
      Proof.
        intros P HP.
        unfold pure_predicate_action.
        destruct (dec P) as [Himp | Hnot].
        - reflexivity.
        - exfalso. apply Hnot, HP.
      Qed.
    End OmegaSameDepth.

    (** 3. Omega_veil is the unique (up to equivalence) impossible predicate *)
    Theorem Omega_unique :
      forall P : Omega,
      Is_Impossible P ->
      Omega_equiv P omega_point.
    Proof.
      intro P.
      apply (proj1 (Omega_Univalence P)).
    Qed.

    (** 4. Paradox numbers classify "distance from False" *)
    Theorem paradox_number_measures_distance :
      forall n,
      Is_Impossible (paradox_at n) /\
      Omega_equiv (paradox_at n) omega_point.
    Proof.
      intro n.
      split.
      - apply all_impossible.
      - apply Omega_unique.
        apply all_impossible.
    Qed.

  End OmegaUnivalence.
End DualUnivalence.
