(** * GeometricGroupTheory.v
    Mapping Class Group Action on Impossible Predicates
    ================================================
    A synthetic MCG using AlphaType as the surface.
    Simple closed curves correspond to predicates.
    Mapping classes = bijections on Alphacarrier.
    We prove: paradox depth is invariant under the MCG.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.
Require Import DAO.Theory.Impossibility.ParadoxNumbers.
Require Import DAO.Theory.Impossibility.PureImpossibilitySymmetry.
From DAO.Theory.Impossibility Require Import PureImpossibilitySymmetry.
Require Import Stdlib.Lists.List.
Import ListNotations.

Import PureImpossibilitySymmetry.PureImpossibilitySymmetry.


Include PureImpossibilitySymmetry.

Module SyntheticMCG.
  Import ParadoxNumbers ParadoxNaturals.
  Import ImpossibilityAlgebra Core.

  Section MCG.
    Context {Alpha : AlphaType}.

    (** --------------------------------------------------------------- *)
    (** 1. “Surface” Structure
        In the synthetic setting, the surface Σ is just the carrier.
    *)

    Definition Surface := Alphacarrier.

    (** A “simple closed curve” is any predicate on Σ.
        Later we may restrict to non-empty / non-trivial ones. *)
    Definition curve := Surface -> Prop.

    (** --------------------------------------------------------------- *)
    (** 2. Mapping Class Group Elements

        In classical GGT:
          φ : Σ → Σ is a homeomorphism.
          φ acts on curves by pushforward:   φ_*(γ) = γ ∘ φ^{-1}.

        Here:
          A mapping class is *any bijection* on Alphacarrier.
    *)

    Record mapping_class := {
      phi      : Alphacarrier -> Alphacarrier;
      phi_inv  : Alphacarrier -> Alphacarrier;
      phi_left_inv  : forall a, phi (phi_inv a) = a;
      phi_right_inv : forall a, phi_inv (phi a) = a;

      phi_preserves_omega :
        forall a, omega_veil (phi a) <-> omega_veil a
    }.

    Lemma phi_inv_preserves_omega (f : mapping_class) :
      forall a, omega_veil (phi_inv f a) <-> omega_veil a.
    Proof.
      intro a.
      (* use phi_preserves_omega at (phi_inv f a) and the left inverse *)
      specialize (phi_preserves_omega f (phi_inv f a)) as H.
      rewrite phi_left_inv in H.
      symmetry.
      exact H.
    Qed.


    Definition Is_Impossible (P : Alphacarrier -> Prop) : Prop :=
      forall a, P a <-> omega_veil a.

    Definition predicate_transform :=
      (Alphacarrier -> Prop) -> (Alphacarrier -> Prop).

    Definition preserves_impossibility (T : predicate_transform) : Prop :=
      forall P, Is_Impossible P -> Is_Impossible (T P).

    (** Pushforward of a curve under φ *)
    Definition pushforward (f : mapping_class)
                          (γ : Alphacarrier -> Prop)
                          : Alphacarrier -> Prop :=
      fun a => γ (phi_inv f a).

    (** --------------------------------------------------------------- *)
    (** 3. Mapping Classes Preserve Impossibility

        A huge win:
          Every bijection induces impossibility preservation.

        Reason:
          If γ has no witnesses, then γ ∘ φ^{-1} also has no witnesses.
    *)

    Theorem mapping_class_preserves_impossibility :
      forall (f : mapping_class),
      preserves_impossibility (pushforward f).
    Proof.
      intros f γ Hγ.  (* Hγ : Is_Impossible γ *)
      unfold Is_Impossible in *.
      intro a.
      specialize (Hγ (phi_inv f a)).
      destruct Hγ as [Hγ_to_ω Hω_to_γ].  (* γ (phi_inv f a) <-> omega_veil (phi_inv f a) *)
      pose proof (phi_inv_preserves_omega f a) as Hω_inv.
      destruct Hω_inv as [Hω_inv_fwd Hω_inv_bwd]. (* omega_veil (phi_inv f a) <-> omega_veil a *)
      split.
      - (* direction: pushforward f γ a -> omega_veil a *)
        intro Hpf.
        unfold pushforward in Hpf.                (* Hpf : γ (phi_inv f a) *)
        apply Hω_inv_fwd.                         (* want omega_veil (phi_inv f a) -> omega_veil a *)
        apply Hγ_to_ω.                            (* γ (phi_inv f a) -> omega_veil (phi_inv f a) *)
        exact Hpf.
      - (* direction: omega_veil a -> pushforward f γ a *)
        intro Hωa.
        unfold pushforward.
        apply Hω_to_γ.                            (* omega_veil (phi_inv f a) -> γ (phi_inv f a) *)
        apply Hω_inv_bwd.                         (* omega_veil a -> omega_veil (phi_inv f a) *)
        exact Hωa.
    Qed.


    (** --------------------------------------------------------------- *)
    (** 4. Paradox Depth of a Curve = false-depth of its impossibility *)

    Hypothesis impossible_decidable :
      forall P : curve, {Is_Impossible P} + {~ Is_Impossible P}.

    Definition curve_depth (γ : curve) : PNat :=
      if impossible_decidable γ then POne else PS POne.

    (** --------------------------------------------------------------- *)
    (** 5. Main Result: Mapping Classes Preserve Paradox Depth *)

    Lemma mapping_class_preserves_impossibility_backwards :
      forall (f : mapping_class) (γ : curve),
      Is_Impossible (pushforward f γ) -> Is_Impossible γ.
    Proof.
      intros f γ Hpush a.
      (* Hpush : Is_Impossible (pushforward f γ) *)
      (* Goal: γ a <-> omega_veil a *)
      specialize (Hpush (phi f a)).
      destruct Hpush as [Hpf_to_ω Hω_to_pf].
      (* Hpf_to_ω : pushforward f γ (phi f a) -> omega_veil (phi f a)
        Hω_to_pf : omega_veil (phi f a) -> pushforward f γ (phi f a)
      *)
      unfold pushforward in *.
      rewrite phi_right_inv in Hpf_to_ω, Hω_to_pf.
      (* now:
          Hpf_to_ω : γ a -> omega_veil (phi f a)
          Hω_to_pf : omega_veil (phi f a) -> γ a
      *)
      specialize (phi_preserves_omega f a) as Hω.
      destruct Hω as [Hω_phi_to_ω Hω_ω_to_phi].
      (* Hω_phi_to_ω : omega_veil (phi f a) -> omega_veil a
        Hω_ω_to_phi : omega_veil a -> omega_veil (phi f a)
      *)
      split.
      - (* γ a -> omega_veil a *)
        intro Hγa.
        apply Hω_phi_to_ω.
        apply Hpf_to_ω.
        exact Hγa.
      - (* omega_veil a -> γ a *)
        intro Hωa.
        apply Hω_to_pf.
        apply Hω_ω_to_phi.
        exact Hωa.
    Qed.

    Theorem mapping_class_invariant_depth :
      forall (f : mapping_class) (γ : curve),
      curve_depth γ = curve_depth (pushforward f γ).
    Proof.
      intros f γ.
      unfold curve_depth.
      destruct (impossible_decidable γ) as [Hγ | Hγ].
      - (* γ impossible *)
        destruct (impossible_decidable (pushforward f γ)) as [Hf | Hf].
        + reflexivity.
        + exfalso.
          apply Hf.
          apply (mapping_class_preserves_impossibility f γ).
          exact Hγ.
      - (* γ possible *)
        destruct (impossible_decidable (pushforward f γ)) as [Hf | Hf].
        + exfalso.
          apply Hγ.
          apply (mapping_class_preserves_impossibility_backwards f γ).
          exact Hf.
        + reflexivity.
    Qed.

    (** --------------------------------------------------------------- *)
    (** 6. This is the Noether Charge for GGT

        Interpretation:

        - φ acts on curves by pushforward.
        - impossibility is invariant under pushforward.
        - therefore false-depth (“paradox number”) is conserved.

        In classical geometric group theory:

          φ ∈ MCG(Σ)
          γ = simple closed curve
          i(γ) = some topological invariant (intersection, genus…)

        Here:
          depth(γ) is a *synthetic logical invariant*.
    *)

    Theorem MCG_noether_charge :
      forall f : mapping_class,
      forall γ : curve,
        curve_depth γ = curve_depth (pushforward f γ).
    Proof.
      apply mapping_class_invariant_depth.
    Qed.

    (** --------------------------------------------------------------- *)
    (** 7. Bonus: The MCG acts as automorphisms of paradox-depth *)

    Definition mcg_action (f : mapping_class) : curve -> curve :=
      pushforward f.

    Theorem mcg_action_is_depth_preserving :
      forall f, preserves_impossibility (mcg_action f).
    Proof.
      intros f. apply mapping_class_preserves_impossibility.
    Qed.

  End MCG.

End SyntheticMCG.
