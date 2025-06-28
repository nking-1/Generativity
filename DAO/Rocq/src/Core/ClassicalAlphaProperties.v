Require Import DAO.Core.ClassicalAlphaType.

(* This file defines the classical properties of the ClassicalAlphaType, which
   is a type that embodies classical logic with a single impossible predicate. *)

(* The impossible predicate is defined as a specific proposition that cannot be true *)

Theorem alpha_embodies_excluded_middle `{H_N: ClassicalAlphaType} :
 forall P : Prop, P \/ ~ P.
Proof.
 exact alpha_constant_decision.
Qed.

(* Double negation elimination follows from excluded middle *)
Theorem alpha_double_negation_elimination `{H_N: ClassicalAlphaType} :
 forall P : Prop, ~~P -> P.
Proof.
 intros P H_nnP.
 destruct (alpha_constant_decision P) as [HP | HnP].
 - exact HP.
 - exfalso. exact (H_nnP HnP).
Qed.

(* Basic properties of the impossible predicate *)

Lemma classical_veil_is_impossible `{H_N: ClassicalAlphaType} :
 forall x: Alphacarrier, ~ classical_veil x.
Proof.
 intros x.
 unfold classical_veil.
 exact (proj1 (proj2_sig alpha_impossibility) x).
Qed.

Lemma classical_veil_unique `{H_N: ClassicalAlphaType} :
 forall P: Alphacarrier -> Prop,
   (forall x: Alphacarrier, ~ P x) -> 
   (forall x: Alphacarrier, P x <-> classical_veil x).
Proof.
 intros P HP.
 unfold classical_veil.
 destruct alpha_impossibility as [Q [HQ HUnique]].
 simpl.
 exact (HUnique P HP).
Qed.

(* Not everything can be impossible *)
Theorem not_everything_is_impossible `{H_N: ClassicalAlphaType} :
 ~ (forall P: Alphacarrier -> Prop, forall x: Alphacarrier, ~ P x).
Proof.
 intros H_all_impossible.
 destruct alpha_not_empty as [x0 _].
 set (always_true := fun x: Alphacarrier => True).
 specialize (H_all_impossible always_true x0).
 exact (H_all_impossible I).
Qed.

(* Define predicate equivalence *)
Definition pred_equiv `{H_N: ClassicalAlphaType} (P Q : Alphacarrier -> Prop) :=
 forall x, P x <-> Q x.

(* The fundamental theorem: using classical logic, every predicate that isn't
  classical_veil must have witnesses *)
Theorem alpha_partial_completeness `{H_N: ClassicalAlphaType} :
 forall P: Alphacarrier -> Prop,
   ~(pred_equiv P classical_veil) ->
   exists x: Alphacarrier, P x.
Proof.
 intros P H_not_equiv.
 (* Use classical logic to decide if P has witnesses *)
 destruct (alpha_constant_decision (exists x, P x)) as [H_exists | H_not_exists].
 - exact H_exists.
 - exfalso.
   apply H_not_equiv.
   unfold pred_equiv.
   apply classical_veil_unique.
   intros x Px.
   apply H_not_exists.
   exists x. exact Px.
Qed.

(* The dichotomy theorem: every predicate either equals classical_veil or has witnesses *)
Theorem everything_possible_except_one `{H_N: ClassicalAlphaType} :
 forall P: Alphacarrier -> Prop,
   pred_equiv P classical_veil \/ exists x: Alphacarrier, P x.
Proof.
 intro P.
 (* Use classical logic *)
 destruct (alpha_constant_decision (exists x, P x)) as [H_exists | H_not_exists].
 - right. exact H_exists.
 - left. 
   unfold pred_equiv.
   apply classical_veil_unique.
   intros x Px.
   apply H_not_exists.
   exists x. exact Px.
Qed.

(* Spatial characterization of ClassicalAlphaType *)
Theorem alpha_is_spatial `{H_N: ClassicalAlphaType} :
 forall P Q: Alphacarrier -> Prop,
   pred_equiv P classical_veil \/ 
   pred_equiv Q classical_veil \/ 
   (exists x, P x) \/ 
   (exists x, Q x) \/
   (exists x, P x /\ Q x).
Proof.
 intros P Q.
 destruct (everything_possible_except_one P) as [HP | [x HPx]].
 - left. exact HP.
 - destruct (everything_possible_except_one Q) as [HQ | [y HQy]].
   + right. left. exact HQ.
   + (* Both P and Q have witnesses *)
     destruct (alpha_constant_decision (exists z, P z /\ Q z)) as [H_overlap | H_disjoint].
     * right. right. right. right. exact H_overlap.
     * right. right. left. exists x. exact HPx.
Qed.

(* The relationship between classical logic and the one-hole structure:
  
  This file demonstrates that ClassicalAlphaType, with its single impossible predicate
  and classical logic for propositions, provides a natural foundation for
  classical reasoning about predicates. Every predicate either falls into
  the unique "hole" (classical_veil) or has witnesses - there is no middle ground.
  
  The spatial nature of ClassicalAlphaType shows how classical logic organizes predicates
  not through temporal evolution (as in some paraconsistent systems) but through
  spatial relationships: predicates either coincide with the impossible, 
  have disjoint witnesses, or overlap in their truth regions.
*)


Theorem predicate_polarity_trichotomy `{ClassicalAlphaType} :
  forall (P : Alphacarrier -> Prop),
    pred_equiv P classical_veil \/
    pred_equiv (fun x => ~ P x) classical_veil \/
    (exists x, P x) /\ (exists y, ~ P y).
Proof.
  intros P.
  destruct (alpha_constant_decision (exists x, P x)) as [Hex | Hnex].
  - (* Case: P has a witness *)
    destruct (alpha_constant_decision (exists x, ~ P x)) as [Hneg | Hnoneg].
    + (* Both P and ~P have witnesses *)
      right. right. split; assumption.
    + (* ~P has no witness => ¬P ≡ classical_veil *)
      right. left.
      unfold pred_equiv, classical_veil.
      apply classical_veil_unique.
      intros x HnegPx.
      apply Hnoneg. exists x. exact HnegPx.
  - (* P has no witness => P ≡ classical_veil *)
    left.
    unfold pred_equiv, classical_veil.
    apply classical_veil_unique.
    intros x Px.
    apply Hnex. exists x. exact Px.
Qed.


Lemma impossible_at : forall `{ClassicalAlphaType} x,
  classical_veil x <-> False.
Proof.
  intros. unfold classical_veil.
  split.
  - apply (proj1 (proj2_sig alpha_impossibility)).
  - intro F. destruct F.
Qed.

