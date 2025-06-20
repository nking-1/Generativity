Require Import Setoid.

Class AlphaSet := {
  Alphacarrier : Type;
  exists_in_Alpha : Alphacarrier -> Prop;
  
  (* The unique impossible predicate - using pointwise equivalence *)
  alpha_impossibility : {P: Alphacarrier -> Prop | 
    (forall x: Alphacarrier, ~ P x) /\
    (forall Q: Alphacarrier -> Prop, 
      (forall x: Alphacarrier, ~ Q x) -> 
      (forall x: Alphacarrier, Q x <-> P x))};
  
  (* Non-emptiness *)
  alpha_not_empty : exists x: Alphacarrier, True;
  
  (* THE DECISION PRINCIPLE: For any predicate, we can decide its status *)
  alpha_decision : forall P : Alphacarrier -> Prop,
    {exists x, P x} + {forall x, ~ P x}
}.

(* Extract the impossible predicate *)
Definition the_impossible `{H_N: AlphaSet} : Alphacarrier -> Prop :=
  proj1_sig alpha_impossibility.

(* Now let's prove everything CONSTRUCTIVELY *)

Lemma the_impossible_is_impossible `{H_N: AlphaSet} :
  forall x: Alphacarrier, ~ the_impossible x.
Proof.
  intros x.
  unfold the_impossible.
  (* Get the proof from the sig type *)
  exact (proj1 (proj2_sig alpha_impossibility) x).
Qed.

Lemma the_impossible_unique `{H_N: AlphaSet} :
  forall P: Alphacarrier -> Prop,
    (forall x: Alphacarrier, ~ P x) -> 
    (forall x: Alphacarrier, P x <-> the_impossible x).
Proof.
  intros P HP.
  unfold the_impossible.
  destruct alpha_impossibility as [Q [HQ HUnique]].
  simpl.
  exact (HUnique P HP).
Qed.

(* HERE'S THE BIG ONE - No classic needed! *)
Theorem alpha_partial_completeness `{H_N: AlphaSet} :
  forall P: Alphacarrier -> Prop,
    ~(forall x, P x <-> the_impossible x) ->
    exists x: Alphacarrier, P x.
Proof.
  intros P H_not_impossible.
  destruct (alpha_decision P) as [H_exists | H_forall_not].
  - exact H_exists.
  - exfalso.
    apply H_not_impossible.
    apply the_impossible_unique.
    exact H_forall_not.
Qed.

(* And now... we DERIVE classical logic! *)
Theorem alpha_generates_excluded_middle `{H_N: AlphaSet} :
  forall P : Prop, P \/ ~ P.
Proof.
  intros P.
  destruct alpha_not_empty as [x0 _].
  
  (* The constant predicate trick *)
  set (const_P := fun _ : Alphacarrier => P).
  
  (* Use the decision principle *)
  destruct (alpha_decision const_P) as [H_yes | H_no].
  - (* If const_P has a witness, then P holds *)
    left.
    destruct H_yes as [x Hx].
    exact Hx.
  - (* If const_P has no witness, then ~P *)
    right.
    intro p.
    apply (H_no x0).
    exact p.
Qed.

(* We can even derive the principle of indirect proof *)
Theorem alpha_generates_double_negation_elimination `{H_N: AlphaSet} :
  forall P : Prop, ~~P -> P.
Proof.
  intros P H_nnP.
  destruct (alpha_generates_excluded_middle P) as [HP | HnP].
  - exact HP.
  - exfalso. exact (H_nnP HnP).
Qed.


(* This one stays the same - it's already constructive *)
Theorem not_everything_is_impossible `{H_N: AlphaSet} :
  ~ (forall P: Alphacarrier -> Prop, forall x: Alphacarrier, ~ P x).
Proof.
  intros H_all_impossible.
  destruct alpha_not_empty as [x0 _].
  set (always_true := fun x: Alphacarrier => True).
  specialize (H_all_impossible always_true x0).
  exact (H_all_impossible I).
Qed.

(* Now let's handle predicate equality properly *)
(* First, let's define when two predicates are equivalent *)
Definition pred_equiv `{H_N: AlphaSet} (P Q : Alphacarrier -> Prop) :=
  forall x, P x <-> Q x.

(* For everything_possible_except_one, we need to decide predicate equivalence *)
(* Let's derive a decision principle for predicate equivalence to the_impossible *)
Lemma decide_if_impossible `{H_N: AlphaSet} :
  forall P : Alphacarrier -> Prop,
    {pred_equiv P the_impossible} + {~ pred_equiv P the_impossible}.
Proof.
  intro P.
  destruct (alpha_decision P) as [H_exists | H_forall_not].
  - (* P has a witness, so it's not the_impossible *)
    right.
    intro H_equiv.
    destruct H_exists as [x Hx].
    (* Use the equivalence at point x *)
    assert (the_impossible x).
    { unfold pred_equiv in H_equiv.
      specialize (H_equiv x).
      destruct H_equiv as [H_to_impossible _].
      exact (H_to_impossible Hx). }
    exact (the_impossible_is_impossible x H).
  - (* P has no witnesses, so it is the_impossible *)
    left.
    unfold pred_equiv.
    apply the_impossible_unique.
    exact H_forall_not.
Qed.

(* NOW we can prove everything_possible_except_one constructively! *)
Theorem everything_possible_except_one `{H_N: AlphaSet} :
  forall P: Alphacarrier -> Prop,
    pred_equiv P the_impossible \/ exists x: Alphacarrier, P x.
Proof.
  intro P.
  destruct (decide_if_impossible P) as [H_eq | H_neq].
  - left. exact H_eq.
  - right. apply alpha_partial_completeness. exact H_neq.
Qed.

(* And here's a bonus - we can derive the law of excluded middle for ANY predicate equality! *)
Theorem alpha_generates_predicate_decidability `{H_N: AlphaSet} :
  forall P Q : Alphacarrier -> Prop,
    (forall x, ~ Q x) ->
    {pred_equiv P Q} + {~ pred_equiv P Q}.
Proof.
  intros P Q HQ_impossible.
  (* Q is impossible, so it's equivalent to the_impossible *)
  assert (Q_eq_impossible : pred_equiv Q the_impossible).
  { unfold pred_equiv.
    exact (the_impossible_unique Q HQ_impossible). }
  
  (* Now we can decide if P is equivalent to the_impossible *)
  destruct (decide_if_impossible P) as [H_yes | H_no].
  - left.
    unfold pred_equiv in *.
    intros x.
    specialize (Q_eq_impossible x).
    specialize (H_yes x).
    split.
    + intro HPx.
      destruct H_yes as [H_to_imp _].
      destruct Q_eq_impossible as [_ imp_to_Q].
      exact (imp_to_Q (H_to_imp HPx)).
    + intro HQx.
      destruct Q_eq_impossible as [Q_to_imp _].
      destruct H_yes as [_ imp_to_P].
      exact (imp_to_P (Q_to_imp HQx)).
  - right.
    intro H_PQ.
    apply H_no.
    unfold pred_equiv in *.
    intros x.
    specialize (H_PQ x).
    specialize (Q_eq_impossible x).
    split.
    + intro HPx.
      destruct H_PQ as [H_PQ_fwd _].
      destruct Q_eq_impossible as [Q_to_imp _].
      exact (Q_to_imp (H_PQ_fwd HPx)).
    + intro H_imp_x.
      destruct Q_eq_impossible as [_ imp_to_Q].
      destruct H_PQ as [_ H_PQ_bwd].
      exact (H_PQ_bwd (imp_to_Q H_imp_x)).
Qed.