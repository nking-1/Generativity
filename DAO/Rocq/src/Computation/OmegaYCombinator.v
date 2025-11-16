(** OmegaYCombinator.v
    Extracting a fixed-point operator (semantic Y-combinator)
    from the completeness axiom of OmegaType.
*)

Require Import DAO.Core.OmegaType.

Module OmegaFixedPoint.

  Section FixedPoints.
    Context `{Omega : OmegaType}.

    (** A fixed point of f : O -> O is an x : O such that f x = x *)
    Definition is_fixed_point (f : Omegacarrier -> Omegacarrier)
                              (x : Omegacarrier) : Prop :=
      f x = x.

    (** Define the predicate "being a fixed point of f" *)
    Definition fixed_point_pred
      (f : Omegacarrier -> Omegacarrier) : Omegacarrier -> Prop :=
      fun x => f x = x.

    (** === THE MAIN THEOREM === *)
    (** Omega’s completeness axiom implies:
        Every function has a fixed point. *)
    Theorem omega_has_fixed_point :
      forall f : Omegacarrier -> Omegacarrier,
        exists x : Omegacarrier, is_fixed_point f x.
    Proof.
      intro f.
      unfold is_fixed_point, fixed_point_pred.
      apply omega_completeness.
    Qed.

    (** This is EXACTLY the semantic Y-combinator.
        It says: for any endomap f, there exists an x such that f x = x. *)

    (** We can even define a FIXED-POINT OPERATOR (a selector): *)

    Definition Y (f : Omegacarrier -> Omegacarrier) : Omegacarrier :=
      match (omega_has_fixed_point f) with
      | ex_intro _ x _ => x
      end.

    (** And it satisfies the fixed-point equation: *)
    Theorem Y_is_fixed_point :
      forall f, is_fixed_point f (Y f).
    Proof.
      intro f.
      unfold Y.
      destruct (omega_has_fixed_point f) as [x Hx].
      exact Hx.
    Qed.

    (** That’s the full analogue of the classical Y combinator:
        Y f = f (Y f).
        Except in our case, equality, not β-equivalence.
    *)

  End FixedPoints.

End OmegaFixedPoint.
