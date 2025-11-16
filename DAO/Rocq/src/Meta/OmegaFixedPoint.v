(** OmegaFixedPoint.v
    ==================

    This module shows how OmegaType's completeness axiom already
    *semantically* contains a fixed-point principle:

      - For every endofunction [f : Omegacarrier -> Omegacarrier],
        there exists a point [x] such that [f x = x].

    This is the semantic analogue of the Y combinator: every self-map
    on Omega has a fixed point, even though we cannot in general define
    a single *computable* [Y : (O -> O) -> O] that picks one.

    Philosophically:
      - Alpha stays consistent by *not* having such a principle.
      - Omega trivializes all such fixed points by completeness.
*)

Require Import DAO.Core.OmegaType.

Module OmegaFixedPoint.

  Section FixedPoints.
    Context {Omega : OmegaType}.

    (** A simple definition: [x] is a fixed point of [f] if [f x = x]. *)
    Definition FixpointOf (f : Omegacarrier -> Omegacarrier)
                          (x : Omegacarrier) : Prop :=
      f x = x.

    (** Core theorem: every self-map on [Omegacarrier] has a fixed point.

        This is the "semantic Y-combinator":
        for any [f], there exists [x] s.t. [f x = x].
     *)
    Theorem omega_has_fixed_point :
      forall f : Omegacarrier -> Omegacarrier,
      exists x : Omegacarrier, FixpointOf f x.
    Proof.
      intros f.
      unfold FixpointOf.
      (* Apply Omega's completeness to the predicate "being a fixed point of f" *)
      destruct (omega_completeness (fun x => f x = x)) as [x Hx].
      exists x; exact Hx.
    Qed.

    (** Slightly rephrased version without the [FixpointOf] wrapper. *)
    Theorem omega_has_pointwise_Y :
      forall f : Omegacarrier -> Omegacarrier,
      exists x : Omegacarrier, f x = x.
    Proof.
      apply omega_has_fixed_point.
    Qed.

    (** Note:
        We *cannot* in general define a global combinator

          Y : (Omegacarrier -> Omegacarrier) -> Omegacarrier

        in this constructive setting, because [omega_completeness] only
        gives us:

          forall P : Omegacarrier -> Prop, exists x, P x

        but not a *choice function* that picks such an [x] uniformly.

        So what we do have is:

          (forall f, exists x, f x = x)

        which is the logical/fixed-point principle behind the Y combinator,
        but not an explicit term-level Y.

        This is exactly the kind of distinction between:

          - "Every recursive equation has a solution" (semantic)
          - "Here is a uniform operator that computes those solutions" (syntactic)

        Omega gives us the former, not necessarily the latter.
     *)

  End FixedPoints.

End OmegaFixedPoint.
