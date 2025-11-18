(**
  =====================================================================
   "Gateway" Theorem: omega_veil as the canonical reference to the Host
  =====================================================================

  Intent
  ------
  We show, *constructively*, that for any Alpha-like substructure living
  inside a richer host (not necessarily Omega; no classical axioms),
  there is a canonical "gateway" predicate — a pointwise equivalent
  representative of the unique-impossible predicate — that plays the
  role of a fixed reference to what lies *beyond* the substructure.

  The only mild extra ingredient we assume about a given "collection"
  C of predicates (think: what the current stage can talk about) is
  that C contains the membership predicate of the substructure itself.
  Under that assumption, the anti-totality predicate relative to C
  has *no witnesses inside the substructure*, so by uniqueness of
  impossibility it *is* the impossible predicate up to ↔.

  This captures precisely the "omega_veil" idea: from within Alpha,
  the one place you can safely point at the beyond is the unique
  impossibility; any attempt to reify “the whole you’re in” (its
  totality) collapses into that veil at the boundary.

  Notes
  -----
  • Entirely intuitionistic: no use of Excluded Middle, etc.
  • We do *not* assume any Omega completeness here.
  • We stay in pointwise equivalence (↔), so no functional
    extensionality is needed.
*)

Require Import Coq.Logic.PropExtensionality  (* not used; here just to signal we avoid it *).

Section Gateway.

  (** Host carrier and an Alpha-like substructure *)
  Variable Carrier : Type.
  Variable A : Carrier -> Prop.  (* the substructure's membership predicate *)

  (** The Alpha-like structure on A:
      - nonempty
      - a chosen "impossible" predicate imp with:
          (i) no witnesses *inside A*
         (ii) uniqueness: any predicate with no A-witnesses is pointwise ↔ imp on A
  *)
  Variable A_nonempty : exists x, A x.

  Variable imp : Carrier -> Prop.
  Hypothesis imp_no_witnesses : forall x, A x -> ~ imp x.
  Hypothesis imp_unique :
    forall Q : Carrier -> Prop,
      (forall x, A x -> ~ Q x) ->
      (forall x, A x -> (Q x <-> imp x)).

  (** Collections and (restricted) totality *)
  Definition Collection := (Carrier -> Prop) -> Prop.

  (* totality of C: the usual “some member predicate holds of a” *)
  Definition totality_of (C : Collection) : Carrier -> Prop :=
    fun a => exists P, C P /\ P a.

  (** The *anti*-totality for C, but explicitly restricted to A:
      Gateway_C a :=  A a -> ~ totality_of C a
      Reading: "From within A, 'not being in C’s totality'".
      We use the implication form so Gateway_C is trivially meaningful
      for all a: outside A it imposes no constraint.
  *)
  Definition Gateway (C : Collection) : Carrier -> Prop :=
    fun a => A a -> ~ totality_of C a.

  (** Mild, constructive assumption tying C to A:
      the collection C is aware of (contains) the membership predicate A.
      This is the only place we relate "what A can talk about" to A itself.
  *)
  Hypothesis C_contains_A : forall (C : Collection), C A -> True.
  (* We’ll use C A as an *assumption* where needed; the hypothesis above
     is just a placeholder to stress it’s not logically heavy. To get
     the main theorem we’ll quantify over C with (C A) as premise. *)

  (** Core Lemma: If a collection C contains A itself,
      then Gateway C has *no witnesses inside A*.
      Proof idea: If A a, then since C contains A, totality_of C a holds
      (via P := A), so (A a -> ~ totality_of C a) cannot hold at that a.
  *)
  Lemma Gateway_has_no_A_witnesses :
    forall (C : Collection),
    C A ->
    forall a, A a -> ~ Gateway C a.
  Proof.
    intros C CA a Ha G.
    unfold Gateway in G.
    (* From C containing A and A a, totality_of C a holds *)
    assert (T : totality_of C a).
    { exists A. split; [assumption| exact Ha]. }
    (* But G says: A a -> ~ totality_of C a *)
    specialize (G Ha).
    exact (G T).
  Qed.

  (** Gateway ≡ imp on A:
      Uniqueness of the impossible predicate now identifies Gateway C
      (which we just showed has no A-witnesses) with imp, pointwise on A.
  *)
  Theorem Gateway_is_imp_on_A :
    forall (C : Collection),
    C A ->
    forall a, A a -> (Gateway C a <-> imp a).
  Proof.
    intros C CA a Ha.
    
    (* imp_unique gives us: 
      (forall x, A x -> ~ Gateway C x) -> 
      (forall x, A x -> Gateway C x <-> imp x)
      
      We want the conclusion at a and Ha specifically.
    *)
    
    (* First, get the implication from imp_unique *)
    assert (H_equiv : forall x, A x -> (Gateway C x <-> imp x)).
    {
      apply imp_unique.
      (* Show Gateway C has no A-witnesses *)
      intros x HAx GWx.
      eapply (Gateway_has_no_A_witnesses C CA x HAx).
      exact GWx.
    }
    
    (* Now apply to our specific a and Ha *)
    apply H_equiv.
    exact Ha.
  Qed.

  (** Invariance wrt changing the collection:
      As long as the collection contains A, the “gateway” *doesn’t depend*
      on which particular C you chose — it is always imp on A.
  *)
  Theorem Gateway_is_canonical_on_A :
    forall (C1 C2 : Collection),
    C1 A -> C2 A ->
    forall a, A a -> (Gateway C1 a <-> Gateway C2 a).
  Proof.
    intros C1 C2 HC1 HC2 a Ha.
    (* Both sides are ↔ imp a on A *)
    transitivity (imp a).
    - apply Gateway_is_imp_on_A; assumption.
    - symmetry. apply Gateway_is_imp_on_A; assumption.
  Qed.

  (** “Fixed-point of reference” phrasing:
      Any attempt to form a ‘totality boundary’ (anti-totality) for any
      A-aware collection C collapses, on A, to the same predicate — imp.
      That is, imp is the *unique* stable reference to “what A cannot
      internalize of its own totality,” i.e. the veil.
  *)
  Corollary Imp_is_fixed_gateway :
    forall (C : Collection),
    C A ->
    forall a, A a -> (Gateway C a <-> Gateway C a /\ imp a).
  Proof.
    intros C CA a Ha.
    rewrite (Gateway_is_imp_on_A C CA a Ha).
    split; intro H; [split; [assumption|assumption] | tauto].
  Qed.

End Gateway.
