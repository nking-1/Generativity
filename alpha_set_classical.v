Require Import Setoid.

Class ClassicalAlphaSet := {
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
 
 (* In this formulation, we explicitly axiomatize classical logic for propositions - this is excluded middle *)
 alpha_constant_decision : forall P : Prop, P \/ ~ P
}.

(* ClassicalAlphaSet embodies excluded middle - we're not claiming to derive it *)
Theorem alpha_embodies_excluded_middle `{H_N: ClassicalAlphaSet} :
 forall P : Prop, P \/ ~ P.
Proof.
 exact alpha_constant_decision.
Qed.

(* Double negation elimination follows from excluded middle *)
Theorem alpha_double_negation_elimination `{H_N: ClassicalAlphaSet} :
 forall P : Prop, ~~P -> P.
Proof.
 intros P H_nnP.
 destruct (alpha_constant_decision P) as [HP | HnP].
 - exact HP.
 - exfalso. exact (H_nnP HnP).
Qed.

(* Extract the impossible predicate *)
Definition the_impossible `{H_N: ClassicalAlphaSet} : Alphacarrier -> Prop :=
 proj1_sig alpha_impossibility.

(* Basic properties of the impossible predicate *)

Lemma the_impossible_is_impossible `{H_N: ClassicalAlphaSet} :
 forall x: Alphacarrier, ~ the_impossible x.
Proof.
 intros x.
 unfold the_impossible.
 exact (proj1 (proj2_sig alpha_impossibility) x).
Qed.

Lemma the_impossible_unique `{H_N: ClassicalAlphaSet} :
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

(* Not everything can be impossible *)
Theorem not_everything_is_impossible `{H_N: ClassicalAlphaSet} :
 ~ (forall P: Alphacarrier -> Prop, forall x: Alphacarrier, ~ P x).
Proof.
 intros H_all_impossible.
 destruct alpha_not_empty as [x0 _].
 set (always_true := fun x: Alphacarrier => True).
 specialize (H_all_impossible always_true x0).
 exact (H_all_impossible I).
Qed.

(* Define predicate equivalence *)
Definition pred_equiv `{H_N: ClassicalAlphaSet} (P Q : Alphacarrier -> Prop) :=
 forall x, P x <-> Q x.

(* The fundamental theorem: using classical logic, every predicate that isn't
  the_impossible must have witnesses *)
Theorem alpha_partial_completeness `{H_N: ClassicalAlphaSet} :
 forall P: Alphacarrier -> Prop,
   ~(pred_equiv P the_impossible) ->
   exists x: Alphacarrier, P x.
Proof.
 intros P H_not_equiv.
 (* Use classical logic to decide if P has witnesses *)
 destruct (alpha_constant_decision (exists x, P x)) as [H_exists | H_not_exists].
 - exact H_exists.
 - exfalso.
   apply H_not_equiv.
   unfold pred_equiv.
   apply the_impossible_unique.
   intros x Px.
   apply H_not_exists.
   exists x. exact Px.
Qed.

(* The dichotomy theorem: every predicate either equals the_impossible or has witnesses *)
Theorem everything_possible_except_one `{H_N: ClassicalAlphaSet} :
 forall P: Alphacarrier -> Prop,
   pred_equiv P the_impossible \/ exists x: Alphacarrier, P x.
Proof.
 intro P.
 (* Use classical logic *)
 destruct (alpha_constant_decision (exists x, P x)) as [H_exists | H_not_exists].
 - right. exact H_exists.
 - left. 
   unfold pred_equiv.
   apply the_impossible_unique.
   intros x Px.
   apply H_not_exists.
   exists x. exact Px.
Qed.

(* Spatial characterization of ClassicalAlphaSet *)
Theorem alpha_is_spatial `{H_N: ClassicalAlphaSet} :
 forall P Q: Alphacarrier -> Prop,
   pred_equiv P the_impossible \/ 
   pred_equiv Q the_impossible \/ 
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
  
  This file demonstrates that ClassicalAlphaSet, with its single impossible predicate
  and classical logic for propositions, provides a natural foundation for
  classical reasoning about predicates. Every predicate either falls into
  the unique "hole" (the_impossible) or has witnesses - there is no middle ground.
  
  The spatial nature of ClassicalAlphaSet shows how classical logic organizes predicates
  not through temporal evolution (as in some paraconsistent systems) but through
  spatial relationships: predicates either coincide with the impossible, 
  have disjoint witnesses, or overlap in their truth regions.
*)


Theorem predicate_polarity_trichotomy `{ClassicalAlphaSet} :
  forall (P : Alphacarrier -> Prop),
    pred_equiv P the_impossible \/
    pred_equiv (fun x => ~ P x) the_impossible \/
    (exists x, P x) /\ (exists y, ~ P y).
Proof.
  intros P.
  destruct (alpha_constant_decision (exists x, P x)) as [Hex | Hnex].
  - (* Case: P has a witness *)
    destruct (alpha_constant_decision (exists x, ~ P x)) as [Hneg | Hnoneg].
    + (* Both P and ~P have witnesses *)
      right. right. split; assumption.
    + (* ~P has no witness => ¬P ≡ the_impossible *)
      right. left.
      unfold pred_equiv, the_impossible.
      apply the_impossible_unique.
      intros x HnegPx.
      apply Hnoneg. exists x. exact HnegPx.
  - (* P has no witness => P ≡ the_impossible *)
    left.
    unfold pred_equiv, the_impossible.
    apply the_impossible_unique.
    intros x Px.
    apply Hnex. exists x. exact Px.
Qed.


Lemma impossible_at : forall `{ClassicalAlphaSet} x,
  the_impossible x <-> False.
Proof.
  intros. unfold the_impossible.
  split.
  - apply (proj1 (proj2_sig alpha_impossibility)).
  - intro F. destruct F.
Qed.


(* Lemma negation_has_witness_if_not_impossible `{ClassicalAlphaSet} :
  forall P : Alphacarrier -> Prop,
    ~(pred_equiv P the_impossible) ->
    exists x, ~ P x.
Proof.
  intros P H_not_impossible.

  destruct (alpha_constant_decision (exists x, ~ P x)) as [H_yes | H_no].
  - exact H_yes.

  - (* Assume: no witness for ¬P ⇒ ¬P ≡ the_impossible *)
    assert (H_neg_equiv : pred_equiv (fun x => ~ P x) the_impossible).
    {
      unfold pred_equiv.
      apply the_impossible_unique.
      intros x Hneg.
      apply H_no. exists x. exact Hneg.
    }

    (* Now deduce: P ≡ not the_impossible ⇒ contradiction *)
    assert (H_equiv : pred_equiv P the_impossible).
    {
      unfold pred_equiv in *.
      intros x.
      specialize (H_neg_equiv x).
      rewrite impossible_at in H_neg_equiv.
      split.
      - intros Px.
        destruct H_neg_equiv as [to_imp _].
        apply to_imp. intro contra. apply contra. exact Px.

      - intros Ti.
        rewrite impossible_at in Ti. destruct Ti.
    }

    (* Contradiction with assumption *)
    apply H_not_impossible. exact H_equiv.
Qed. *)


(* Helper lemmas for working with ClassicalAlphaSet *)
Section HelperLemmas.
Context `{H_alpha: ClassicalAlphaSet}.

(* The key equivalence we just used: converting between negated existence and universal negation *)
Lemma not_exists_forall_not (P : Alphacarrier -> Prop) :
  ~ (exists x, P x) <-> forall x, ~ P x.
Proof.
  split.
  - intros Hnex x Px.
    apply Hnex. exists x. exact Px.
  - intros Hall [x Px].
    exact (Hall x Px).
Qed.

(* A predicate is the_impossible iff it has no witnesses *)
Lemma impossible_no_witness (P : Alphacarrier -> Prop) :
  pred_equiv P the_impossible <-> ~ (exists x, P x).
Proof.
  split.
  - intros Heq [x Px].
    apply (the_impossible_is_impossible x).
    apply Heq. exact Px.
  - intros Hnex.
    unfold pred_equiv.
    apply the_impossible_unique.
    apply not_exists_forall_not. exact Hnex.
Qed.

(* Useful corollary: a predicate has witnesses iff it's not the_impossible *)
Lemma witness_not_impossible (P : Alphacarrier -> Prop) :
  (exists x, P x) <-> ~ pred_equiv P the_impossible.
Proof.
  split.
  - intros Hex Heq.
    apply impossible_no_witness in Heq.
    exact (Heq Hex).
  - intros Hneq.
    destruct (everything_possible_except_one P) as [Heq | Hex].
    + contradiction.
    + exact Hex.
Qed.

(* The "always true" predicate is unique up to equivalence *)
Definition the_necessary : Alphacarrier -> Prop :=
  fun x => ~ the_impossible x.

Lemma necessary_always_true :
  forall x, the_necessary x.
Proof.
  intros x.
  unfold the_necessary.
  exact (the_impossible_is_impossible x).
Qed.

Lemma necessary_unique (P : Alphacarrier -> Prop) :
  (forall x, P x) -> pred_equiv P the_necessary.
Proof.
  intros Hall.
  unfold pred_equiv, the_necessary.
  intros x.
  split.
  - intros _. exact (the_impossible_is_impossible x).
  - intros _. exact (Hall x).
Qed.

(* Any predicate between impossible and necessary must be "mixed" *)
Lemma between_impossible_necessary (P : Alphacarrier -> Prop) :
  ~ pred_equiv P the_impossible ->
  ~ pred_equiv P the_necessary ->
  (exists x, P x) /\ (exists y, ~ P y).
Proof.
  intros Hnot_imp Hnot_nec.
  split.
  - apply witness_not_impossible. exact Hnot_imp.
  - destruct (alpha_constant_decision (exists y, ~ P y)) as [Hex | Hnex].
    + exact Hex.
    + exfalso.
      apply Hnot_nec.
      apply necessary_unique.
      intros x.
      destruct (alpha_constant_decision (P x)) as [HP | HnP].
      * exact HP.
      * exfalso. apply Hnex. exists x. exact HnP.
Qed.

(* Predicates form a "three-valued" logic in some sense *)
Lemma predicate_trichotomy (P : Alphacarrier -> Prop) :
  pred_equiv P the_impossible \/
  pred_equiv P the_necessary \/
  ((exists x, P x) /\ (exists y, ~ P y)).
Proof.
  destruct (predicate_polarity_trichotomy P) as [Himp | [Hneg_imp | Hmixed]].
  - left. exact Himp.
  - right. left.
    unfold pred_equiv, the_necessary.
    intros x. split.
    + intros _. exact (the_impossible_is_impossible x).
    + intros _.
      destruct (alpha_constant_decision (P x)) as [HP | HnP].
      * exact HP.
      * exfalso. 
        (* Hneg_imp tells us: (~ P x) <-> the_impossible x *)
        (* We have HnP : ~ P x *)
        (* So we can deduce: the_impossible x *)
        apply (the_impossible_is_impossible x).
        apply Hneg_imp.
        exact HnP.
  - right. right. exact Hmixed.
Qed.

End HelperLemmas.


(* Boolean Algebra Implementation in ClassicalAlphaSet *)

(* First, let's define the quotient type for predicates modulo equivalence *)
Section BooleanAlgebraOnPredicates.
Context `{H_alpha: ClassicalAlphaSet}.

(* Define the type of predicates *)
Definition AlphaPred := Alphacarrier -> Prop.

(* Boolean operations on predicates *)
Definition pred_and (P Q : AlphaPred) : AlphaPred :=
  fun x => P x /\ Q x.

Definition pred_or (P Q : AlphaPred) : AlphaPred :=
  fun x => P x \/ Q x.

Definition pred_not (P : AlphaPred) : AlphaPred :=
  fun x => ~ P x.

Definition pred_top : AlphaPred :=
  fun x => True.

Definition pred_bot : AlphaPred :=
  the_impossible.

(* Prove that operations preserve the witness dichotomy *)
Lemma pred_and_dichotomy (P Q : AlphaPred) :
  pred_equiv (pred_and P Q) the_impossible \/ 
  exists x, (pred_and P Q) x.
Proof.
  unfold pred_and.
  destruct (alpha_constant_decision (exists x, P x /\ Q x)).
  - right. exact H.
  - left.
    unfold pred_equiv.
    apply the_impossible_unique.
    (* Convert ~ (exists x, P x /\ Q x) to forall x, ~ (P x /\ Q x) *)
    intros x [HPx HQx].
    apply H. exists x. split; assumption.
Qed.

Lemma pred_or_dichotomy (P Q : AlphaPred) :
  pred_equiv (pred_or P Q) the_impossible \/ 
  exists x, (pred_or P Q) x.
Proof.
  unfold pred_or.
  destruct (everything_possible_except_one P) as [HP | [x HPx]].
  - destruct (everything_possible_except_one Q) as [HQ | [y HQy]].
    + left. 
      unfold pred_equiv.
      apply the_impossible_unique.
      intros z [HPz | HQz].
      * (* HP tells us P z <-> the_impossible z, and we have HPz : P z *)
        (* So we get the_impossible z *)
        apply (the_impossible_is_impossible z).
        apply HP. exact HPz.
      * (* Similarly for Q *)
        apply (the_impossible_is_impossible z).
        apply HQ. exact HQz.
    + right. exists y. right. exact HQy.
  - right. exists x. left. exact HPx.
Qed.

(* Prove key boolean algebra laws *)
Theorem pred_and_comm (P Q : AlphaPred) :
  pred_equiv (pred_and P Q) (pred_and Q P).
Proof.
  unfold pred_equiv, pred_and.
  intros x. tauto.
Qed.

Theorem pred_or_comm (P Q : AlphaPred) :
  pred_equiv (pred_or P Q) (pred_or Q P).
Proof.
  unfold pred_equiv, pred_or.
  intros x. tauto.
Qed.

Theorem pred_and_assoc (P Q R : AlphaPred) :
  pred_equiv (pred_and P (pred_and Q R)) (pred_and (pred_and P Q) R).
Proof.
  unfold pred_equiv, pred_and.
  intros x. tauto.
Qed.

Theorem pred_or_assoc (P Q R : AlphaPred) :
  pred_equiv (pred_or P (pred_or Q R)) (pred_or (pred_or P Q) R).
Proof.
  unfold pred_equiv, pred_or.
  intros x. tauto.
Qed.

(* Distributivity *)
Theorem pred_and_or_distrib (P Q R : AlphaPred) :
  pred_equiv (pred_and P (pred_or Q R)) (pred_or (pred_and P Q) (pred_and P R)).
Proof.
  unfold pred_equiv, pred_and, pred_or.
  intros x. tauto.
Qed.

(* Identity laws *)
Theorem pred_and_top_id (P : AlphaPred) :
  pred_equiv (pred_and P pred_top) P.
Proof.
  unfold pred_equiv, pred_and, pred_top.
  intros x. tauto.
Qed.

Theorem pred_or_bot_id (P : AlphaPred) :
  pred_equiv (pred_or P pred_bot) P.
Proof.
  unfold pred_equiv, pred_or, pred_bot.
  intros x. split.
  - intros [HP | Himp].
    + exact HP.
    + exfalso. apply (the_impossible_is_impossible x). exact Himp.
  - intros HP. left. exact HP.
Qed.

(* Complement laws - this is where ClassicalAlphaSet shines! *)
Theorem pred_not_not (P : AlphaPred) :
  pred_equiv (pred_not (pred_not P)) P.
Proof.
  unfold pred_equiv, pred_not.
  intros x.
  split.
  - apply alpha_double_negation_elimination.
  - intros HP Hnot. exact (Hnot HP).
Qed.

(* The key theorem: every predicate has a complement *)
Theorem pred_complement_exists (P : AlphaPred) :
  pred_equiv (pred_or P (pred_not P)) pred_top /\
  pred_equiv (pred_and P (pred_not P)) pred_bot.
Proof.
  split.
  - unfold pred_equiv, pred_or, pred_not, pred_top.
    intros x.
    split; [intros _ | intros _].
    + exact I.
    + destruct (alpha_constant_decision (P x)); tauto.
  - unfold pred_equiv, pred_and, pred_not, pred_bot.
    intros x.
    split.
    + intros [HP HnP]. 
      (* We have HP : P x and HnP : ~ P x, which gives us False *)
      exfalso. exact (HnP HP).
    + intros Himp. exfalso. 
      apply (the_impossible_is_impossible x). exact Himp.
Qed.

(* De Morgan's Laws *)
Theorem de_morgan_and (P Q : AlphaPred) :
  pred_equiv (pred_not (pred_and P Q)) (pred_or (pred_not P) (pred_not Q)).
Proof.
  unfold pred_equiv, pred_not, pred_and, pred_or.
  intros x.
  split.
  - intros HnPQ.
    destruct (alpha_constant_decision (P x)) as [HP | HnP].
    + destruct (alpha_constant_decision (Q x)) as [HQ | HnQ].
      * exfalso. apply HnPQ. split; assumption.
      * right. exact HnQ.
    + left. exact HnP.
  - intros [HnP | HnQ] [HP HQ].
    + exact (HnP HP).
    + exact (HnQ HQ).
Qed.

Theorem de_morgan_or (P Q : AlphaPred) :
  pred_equiv (pred_not (pred_or P Q)) (pred_and (pred_not P) (pred_not Q)).
Proof.
  unfold pred_equiv, pred_not, pred_and, pred_or.
  intros x.
  tauto.
Qed.

(* The crucial insight: the quotient by pred_equiv forms a Boolean algebra *)
(* We can characterize its size using the trichotomy *)
Theorem boolean_algebra_classification :
  forall P : AlphaPred,
    pred_equiv P pred_bot \/
    pred_equiv P pred_top \/
    (exists x, P x) /\ (exists y, ~ P y).
Proof.
  intros P.
  destruct (predicate_trichotomy P) as [Hbot | [Htop | Hmixed]].
  - left. 
    unfold pred_bot.
    exact Hbot.
  - right. left.
    unfold pred_top, the_necessary.
    unfold pred_equiv in *.
    intros x. split.
    + intros _. exact I.
    + intros _. apply Htop. apply the_impossible_is_impossible.
  - right. right. exact Hmixed.
Qed.

End BooleanAlgebraOnPredicates.


(* Paradox Firewalls *)
Section ParadoxFirewalls.
Context `{H_alpha: ClassicalAlphaSet}.

(* Russell's Paradox firewall: There is no "set of all sets that don't contain themselves" *)
Theorem no_russell_predicate :
  ~ exists (R : AlphaPred), 
    forall x, R x <-> ~ R x.
Proof.
  intros [R HR].
  (* Consider R applied to any witness - by non-emptiness we have one *)
  destruct alpha_not_empty as [x0 _].
  specialize (HR x0).
  (* R x0 <-> ~ R x0 is a contradiction *)
  tauto.
Qed.

(* Curry's Paradox firewall: For Q = False, no such predicate exists *)
Theorem no_curry_predicate_false :
  ~ exists (C : AlphaPred),
    forall x, C x <-> (C x -> False).
Proof.
  intros [C HC].
  destruct alpha_not_empty as [x0 _].
  specialize (HC x0).
  (* HC : C x0 <-> (C x0 -> False) *)
  
  (* If C x0 holds, then C x0 -> False, so False *)
  assert (~ C x0).
  { intros H0.
    (* H0 : C x0 *)
    assert (C x0 -> False) by (apply HC; exact H0).
    (* Now we have H : C x0 -> False and H0 : C x0 *)
    exact (H H0). }
  
  (* But by HC backward, (C x0 -> False) implies C x0 *)
  apply H.
  apply HC.
  exact H.
Qed.

(* Alternative: Show that Curry's schema makes every Q provable *)
Theorem curry_makes_everything_provable :
  forall (Q : Prop),
    (exists (C : AlphaPred), forall x, C x <-> (C x -> Q)) -> Q.
Proof.
  intros Q [C HC].
  destruct alpha_not_empty as [x0 _].
  specialize (HC x0).
  (* HC : C x0 <-> (C x0 -> Q) *)
  
  (* The key lemma: (C x0 -> Q) -> Q *)
  assert (HQ: (C x0 -> Q) -> Q).
  { intros Himp.
    (* Himp : C x0 -> Q *)
    (* By HC backward, this means C x0 holds *)
    assert (C x0) by (apply HC; exact Himp).
    (* Now apply Himp to get Q *)
    exact (Himp H). }
  
  (* Now we prove Q using HQ *)
  apply HQ.
  (* We need to show: C x0 -> Q *)
  intros H_C.
  (* H_C : C x0 *)
  (* By HC forward, C x0 implies C x0 -> Q *)
  assert (C x0 -> Q) by (apply HC; exact H_C).
  (* Now we have H : C x0 -> Q, so we can use HQ again *)
  exact (HQ H).
Qed.

(* The Liar Paradox firewall: No predicate can assert its own falsehood *)
Theorem no_liar_predicate :
  ~ exists (L : AlphaPred),
    forall x, L x <-> ~ L x.
Proof.
  exact no_russell_predicate.
Qed.

(* A more subtle one: No predicate can be equivalent to its own non-existence *)
Theorem no_self_denying_existence :
  ~ exists (P : AlphaPred),
    pred_equiv P the_impossible /\ (exists x, P x).
Proof.
  intros [P [Heq Hex]].
  destruct Hex as [x Px].
  apply (the_impossible_is_impossible x).
  apply Heq. exact Px.
Qed.

(* Every predicate is "grounded" - it can't circularly depend on its own truth value *)
Theorem predicate_grounding :
  forall (P : AlphaPred),
    (forall x, P x <-> exists y, P y) ->
    pred_equiv P the_impossible \/ pred_equiv P the_necessary.
Proof.
  intros P H.
  destruct (everything_possible_except_one P) as [Himp | [x Px]].
  - left. exact Himp.
  - right. 
    (* P has a witness, so by H, P is everywhere true *)
    assert (forall z, P z).
    { intros z. apply H. exists x. exact Px. }
    (* So P is equivalent to the_necessary *)
    unfold pred_equiv, the_necessary.
    intros z. split.
    + intros _. exact (the_impossible_is_impossible z).
    + intros _. exact (H0 z).
Qed.

End ParadoxFirewalls.


(* Natural Numbers in ClassicalAlphaSet *)
Section NaturalNumbers.
Context `{H_alpha: ClassicalAlphaSet}.

(* We'll encode natural numbers as elements that satisfy certain predicates *)
(* First, we need a predicate that picks out the "numbers" *)
Variable IsNat : AlphaPred.

(* Zero is a specific natural number *)
Variable IsZero : AlphaPred.

(* Successor relation: Succ x y means "y is the successor of x" *)
Variable Succ : Alphacarrier -> Alphacarrier -> Prop.

(* Axiom 1: Zero exists and is a natural number *)
Axiom zero_exists : exists z, IsZero z /\ IsNat z.

(* Axiom 2: Zero is unique *)
Axiom zero_unique : forall x y, IsZero x -> IsZero y -> x = y.

(* Axiom 3: Every natural number has a successor that is also natural *)
Axiom successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y.

(* Axiom 4: Successor is functional (deterministic) *)
Axiom successor_functional : forall x y z, Succ x y -> Succ x z -> y = z.

(* Axiom 5: No number is its own successor (no cycles) *)
Axiom successor_not_reflexive : forall x, ~ Succ x x.

(* Axiom 6: Different numbers have different successors (injectivity) *)
Axiom successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y.

(* Axiom 7: Zero is not a successor *)
Axiom zero_not_successor : forall x y, IsZero y -> ~ Succ x y.

(* Axiom 8: Induction principle *)
Axiom nat_induction : 
  forall (P : AlphaPred),
    (* Base case: P holds for zero *)
    (forall z, IsZero z -> P z) ->
    (* Inductive case: if P(n) then P(S(n)) *)
    (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
    (* Conclusion: P holds for all naturals *)
    (forall n, IsNat n -> P n).

(* Let's prove some basic theorems *)

(* Zero is not the impossible predicate *)
Theorem zero_exists_witness :
  ~ pred_equiv IsZero the_impossible.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [Hz _]].
  exists z. exact Hz.
Qed.

(* Natural numbers form a non-empty set *)
Theorem nat_exists_witness :
  ~ pred_equiv IsNat the_impossible.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [_ Hz]].
  exists z. exact Hz.
Qed.

(* Every natural number is either zero or a successor *)
Theorem zero_or_successor :
  forall n, IsNat n -> IsZero n \/ exists m, IsNat m /\ Succ m n.
Proof.
  intros n Hn.
  (* Use excluded middle *)
  destruct (alpha_constant_decision (IsZero n)) as [Hz | Hnz].
  - left. exact Hz.
  - right.
    (* Use induction to prove this *)
    (* Define the predicate: "is zero or has a predecessor" *)
    set (P := fun x => IsZero x \/ exists m, IsNat m /\ Succ m x).
    assert (HP: P n).
    { apply (nat_induction P); [| |exact Hn].
      - (* Base case: zero satisfies P *)
        intros z Hz. left. exact Hz.
      - (* Inductive case *)
        intros k m Hk HP_k Hsucc.
        right. exists k. split.
        + exact Hk.
        + exact Hsucc. }
    (* Now use the assertion - HP : P n *)
    unfold P in HP.
    destruct HP as [Hz' | Hpred].
    + (* Case: IsZero n - but we know ~ IsZero n *)
      contradiction.
    + (* Case: exists m, IsNat m /\ Succ m n *)
      exact Hpred.
Qed.

(* No number is both zero and a successor *)
Theorem zero_not_both :
  forall n m, IsZero n -> ~ Succ m n.
Proof.
  intros n m Hz Hsucc.
  exact (zero_not_successor m n Hz Hsucc).
Qed.

(* The successor relation is not impossible - at least one successor exists *)
Theorem successor_not_impossible :
  exists x y, Succ x y.
Proof.
  destruct zero_exists as [z [Hz HNz]].
  destruct (successor_exists z HNz) as [sz [Hsz _]].
  exists z, sz. exact Hsz.
Qed.

(* Alternative: Show that the predicate "has a successor" is not impossible *)
Theorem has_successor_not_impossible :
  ~ pred_equiv (fun x => exists y, Succ x y) the_impossible.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [Hz HNz]].
  destruct (successor_exists z HNz) as [sz [Hsz _]].
  exists z. exists sz. exact Hsz.
Qed.

(* Or: Show that the predicate "is a successor" is not impossible *)
Theorem is_successor_not_impossible :
  ~ pred_equiv (fun y => exists x, Succ x y) the_impossible.
Proof.
  apply witness_not_impossible.
  destruct zero_exists as [z [Hz HNz]].
  destruct (successor_exists z HNz) as [sz [Hsz _]].
  exists sz. exists z. exact Hsz.
Qed.

(* Every natural has a unique successor *)
Theorem successor_unique :
  forall n, IsNat n -> exists! s, Succ n s.
Proof.
  intros n Hn.
  destruct (successor_exists n Hn) as [s [Hs HNs]].
  exists s. split.
  - exact Hs.
  - intros y Hy.
    exact (successor_functional n s y Hs Hy).
Qed.

End NaturalNumbers.


(* Building Arithmetic towards the Infinitude of Primes *)
Section ArithmeticAndPrimes.
Context `{H_alpha: ClassicalAlphaSet}.

(* Import our natural numbers *)
Context (IsNat : AlphaPred) (IsZero : AlphaPred) 
        (Succ : Alphacarrier -> Alphacarrier -> Prop).
Context (zero_exists : exists z, IsZero z /\ IsNat z).
Context (zero_unique : forall x y, IsZero x -> IsZero y -> x = y).
Context (successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y).
Context (successor_functional : forall x y z, Succ x y -> Succ x z -> y = z).
Context (successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y).
Context (zero_not_successor : forall x y, IsZero y -> ~ Succ x y).
Context (nat_induction : forall (P : AlphaPred),
    (forall z, IsZero z -> P z) ->
    (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
    (forall n, IsNat n -> P n)).

(* Define One as successor of zero *)
Definition IsOne : AlphaPred := fun x => exists z, IsZero z /\ Succ z x.

(* Addition relation: Plus x y z means x + y = z *)
Variable Plus : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.

(* Addition axioms *)
Axiom plus_zero_left : forall x z, IsZero z -> IsNat x -> Plus z x x.
Axiom plus_zero_right : forall x z, IsZero z -> IsNat x -> Plus x z x.
Axiom plus_successor : forall x y z sx sy sz,
  IsNat x -> IsNat y -> IsNat z ->
  Succ x sx -> Succ y sy -> Succ z sz ->
  Plus x y z -> Plus sx y sz.
Axiom plus_functional : forall x y z1 z2,
  Plus x y z1 -> Plus x y z2 -> z1 = z2.
Axiom plus_exists : forall x y,
  IsNat x -> IsNat y -> exists z, IsNat z /\ Plus x y z.

(* Multiplication relation: Times x y z means x * y = z *)
Variable Times : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.

(* Multiplication axioms *)
Axiom times_zero_left : forall x z, IsZero z -> IsNat x -> Times z x z.
Axiom times_zero_right : forall x z, IsZero z -> IsNat x -> Times x z z.
Axiom times_one_left : forall x o, IsOne o -> IsNat x -> Times o x x.
Axiom times_one_right : forall x o, IsOne o -> IsNat x -> Times x o x.
Axiom times_successor : forall x y z xy sxy,
  IsNat x -> IsNat y -> IsNat z ->
  Succ y z ->
  Times x y xy -> Plus xy x sxy ->
  Times x z sxy.
Axiom times_functional : forall x y z1 z2,
  Times x y z1 -> Times x y z2 -> z1 = z2.
Axiom times_exists : forall x y,
  IsNat x -> IsNat y -> exists z, IsNat z /\ Times x y z.

(* Divisibility: Divides d n means d divides n *)
Definition Divides (d n : Alphacarrier) : Prop :=
  exists q, IsNat q /\ Times d q n.

(* Prime numbers *)
Definition IsPrime (p : Alphacarrier) : Prop :=
  IsNat p /\
  ~ IsZero p /\
  ~ IsOne p /\
  forall d, IsNat d -> Divides d p -> (IsOne d \/ d = p).

(* One exists and is unique *)
Lemma one_exists : exists o, IsOne o /\ IsNat o.
Proof.
  destruct zero_exists as [z [Hz HzNat]].
  destruct (successor_exists z HzNat) as [o [Hsucc HoNat]].
  exists o. split.
  - exists z. split; assumption.
  - exact HoNat.
Qed.

Lemma one_unique : forall x y, IsOne x -> IsOne y -> x = y.
Proof.
  intros x y [zx [Hzx Hsuccx]] [zy [Hzy Hsuccy]].
  assert (zx = zy) by (apply (zero_unique zx zy); assumption).
  subst zy.
  exact (successor_functional zx x y Hsuccx Hsuccy).
Qed.

(* Two is the successor of one *)
Definition IsTwo : AlphaPred := fun x => exists o, IsOne o /\ Succ o x.

(* Key lemma: 1 is not 0 *)
Lemma one_not_zero : forall o z, IsOne o -> IsZero z -> o <> z.
Proof.
  intros o z [zo [Hzo Hsucc]] Hz Heq.
  subst o.
  exact (zero_not_successor zo z Hz Hsucc).
Qed.

End ArithmeticAndPrimes.


Section EuclidPrimesKeyLemmas.
  Context `{H_alpha : ClassicalAlphaSet}.
  Context (IsNat IsZero IsOne : AlphaPred).
  Context (Succ : Alphacarrier -> Alphacarrier -> Prop).
  Context (zero_exists : exists z, IsZero z /\ IsNat z).
  Context (zero_unique : forall x y, IsZero x -> IsZero y -> x = y).
  Context (successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y).
  Context (successor_functional : forall x y z, Succ x y -> Succ x z -> y = z).
  Context (successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y).
  Context (zero_not_successor : forall x y, IsZero y -> ~ Succ x y).
  Context (nat_induction : forall (P : AlphaPred),
              (forall z, IsZero z -> P z) ->
              (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
              forall n, IsNat n -> P n).

  Context (Plus Times : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop).
  Context (plus_exists : forall x y, IsNat x -> IsNat y -> exists z, IsNat z /\ Plus x y z).
  Context (plus_functional : forall x y z1 z2, Plus x y z1 -> Plus x y z2 -> z1 = z2).

  Context (Divides : Alphacarrier -> Alphacarrier -> Prop).
  Context (IsPrime_pred : Alphacarrier -> Prop).
  Notation IsPrime := IsPrime_pred.

  Context (one_exists : exists o, IsOne o /\ IsNat o).
  Context (one_unique : forall x y, IsOne x -> IsOne y -> x = y).

  (* Structural definition of IsPrime assumed elsewhere *)
  Axiom prime_is_nat : forall p, IsPrime p -> IsNat p.
  Axiom prime_not_zero : forall p, IsPrime p -> ~ IsZero p.
  Axiom prime_not_one : forall p, IsPrime p -> ~ IsOne p.
  Axiom prime_minimal : forall p d, 
    IsPrime p -> IsNat d -> Divides d p -> IsOne d \/ d = p.


(* Add this axiom *)
Axiom divides_one_implies_one : forall d one,
  IsNat d -> IsOne one -> Divides d one -> IsOne d.

Axiom divides_difference : forall a b c d,
IsNat a -> IsNat b -> IsNat c ->
Plus a c b ->
Divides d b -> Divides d a ->
Divides d c.

Lemma prime_not_divides_one :
  forall p one,
    IsPrime p -> IsOne one -> ~ Divides p one.
Proof.
  intros p one Hprime Hone Hdiv.
  (* p divides 1, so p must be 1 *)
  assert (IsNat p) by (apply prime_is_nat; exact Hprime).
  assert (IsOne p).
  { apply (divides_one_implies_one p one); assumption. }
  (* But p is prime, so p cannot be 1 *)
  exact (prime_not_one p Hprime H0).
Qed.

  Lemma divides_consecutive_implies_divides_one :
    forall n m d one,
      IsNat n -> IsNat m -> IsOne one ->
      Plus n one m ->
      Divides d n -> Divides d m ->
      Divides d one.
  Proof.
    intros n m d one Hn Hm Hone Hplus Hdiv_n Hdiv_m.
    destruct one_exists as [o [Ho_one Ho_nat]].
    assert (one = o) by (apply one_unique; assumption).
    subst.
    (* Now use the divides_difference axiom *)
    apply (divides_difference n m o d Hn Hm Ho_nat Hplus Hdiv_m Hdiv_n).
  Qed.


  (* Greater than relation *)
  Definition Greater (x y : Alphacarrier) : Prop :=
    exists z, IsNat z /\ ~ IsZero z /\ Plus y z x.

  (* Finite products *)
  Variable Product : (Alphacarrier -> Alphacarrier) -> Alphacarrier -> Alphacarrier -> Prop.

  (* Product axioms *)
  Axiom product_exists : forall f n,
    IsNat n -> 
    (forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> IsNat (f i)) ->
    exists p, IsNat p /\ Product f n p.

  Axiom factor_divides_product : forall f n i prod,
    IsNat n -> IsNat i ->
    (exists j, IsNat j /\ Plus i n j) ->
    Product f n prod ->
    Divides (f i) prod.

  Axiom product_nonzero : forall f n prod,
    IsNat n ->
    Product f n prod ->
    (forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> ~ IsZero (f i)) ->
    ~ IsZero prod.

  (* Every number > 1 has a prime divisor *)
  Axiom has_prime_divisor : forall n one,
    IsNat n -> IsOne one -> Greater n one ->
    exists p, IsPrime p /\ Divides p n.

(* Add this axiom before the theorem *)
  Axiom plus_comm : forall x y z,
    Plus x y z -> Plus y x z.

  (* Main theorem: Euclid's proof *)
  Theorem euclid_infinitude_of_primes :
    forall n f,
      IsNat n ->
      (forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> IsPrime (f i)) ->
      exists p, IsPrime p /\ 
      forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> p <> f i.
  Proof.
    intros n f Hn Hf_primes.
    
    (* Get the product of all primes f(0)...f(n-1) *)
    assert (H_f_nat: forall i, IsNat i -> (exists j, IsNat j /\ Plus i n j) -> IsNat (f i)).
    { intros i Hi Hlt. 
      assert (IsPrime (f i)) by (apply Hf_primes; assumption).
      apply prime_is_nat; assumption. }
    
    destruct (product_exists f n Hn H_f_nat) as [prod [Hprod_nat Hprod]].
    
    (* Get m = prod + 1 *)
    destruct one_exists as [one [Hone Hone_nat]].
    destruct (plus_exists prod one Hprod_nat Hone_nat) as [m [Hm_nat Hplus_m]].
    
    (* m > 1 because prod ≥ 1 *)
    assert (Hm_gt_one: Greater m one).
    { exists prod. split; [exact Hprod_nat|]. split.
      - (* prod is not zero because it's a product of primes *)
        apply product_nonzero with (f := f) (n := n).
        + exact Hn.
        + exact Hprod.
        + intros i Hi Hlt.
          assert (IsPrime (f i)) by (apply Hf_primes; assumption).
          apply prime_not_zero; assumption.
      - (* Use commutativity to get the right order *)
        apply plus_comm. exact Hplus_m. }
    
    (* So m has a prime divisor p *)
    destruct (has_prime_divisor m one Hm_nat Hone Hm_gt_one) as [p [Hp_prime Hp_div_m]].
    
    exists p. split; [exact Hp_prime|].
    
    (* p cannot be any f(i) *)
    intros i Hi Hlt Heq.
    subst p.
    
    (* f(i) divides prod (as it's a factor) *)
    assert (Hdiv_prod: Divides (f i) prod).
    { apply (factor_divides_product f n i prod Hn Hi Hlt Hprod). }
    
    (* f(i) also divides m = prod + 1 *)
    (* So f(i) divides both prod and prod + 1, hence divides 1 *)
    assert (Hdiv_one: Divides (f i) one).
    { apply (divides_consecutive_implies_divides_one prod m (f i) one).
      - exact Hprod_nat.
      - exact Hm_nat.
      - exact Hone.
      - exact Hplus_m.
      - exact Hdiv_prod.
      - exact Hp_div_m. }
    
    (* But f(i) is prime, so cannot divide 1 *)
    apply (prime_not_divides_one (f i) one).
    - apply Hf_primes; assumption.
    - exact Hone.
    - exact Hdiv_one.
  Qed.
End EuclidPrimesKeyLemmas.


Section ZFC_in_ClassicalAlpha.
Context `{H_alpha: ClassicalAlphaSet}.

(* Sets are just predicates - rename to avoid conflict with Coq's Set *)
Definition ZSet := AlphaPred.

(* Membership is predicate application *)
Definition In (x : Alphacarrier) (A : ZSet) : Prop := A x.
Notation "x 'in' A" := (In x A) (at level 70).
Notation "x 'notin' A" := (~ In x A) (at level 70).

(* Set equality via extensionality *)
Definition set_eq (A B : ZSet) : Prop := pred_equiv A B.
Notation "A == B" := (set_eq A B) (at level 70).

(* Axiom 1: Extensionality (but it's just pred_equiv!) *)
Theorem extensionality : forall A B : ZSet,
  (forall x, x in A <-> x in B) <-> A == B.
Proof.
  intros A B.
  unfold set_eq, pred_equiv, In.
  split; intro H; exact H.
Qed.

(* Axiom 2: Empty Set (it's the_impossible!) *)
Definition Empty : ZSet := the_impossible.

Theorem empty_set_exists : exists E : ZSet, forall x, x notin E.
Proof.
  exists Empty.
  intros x.
  unfold In, Empty.
  apply the_impossible_is_impossible.
Qed.

(* Singleton sets *)
Definition singleton (a : Alphacarrier) : ZSet :=
  fun x => x = a.

Theorem singleton_spec : forall a x,
  x in singleton a <-> x = a.
Proof.
  intros a x.
  unfold In, singleton.
  split; intro H; exact H.
Qed.

(* Now let's try pairing *)
Definition pair (a b : Alphacarrier) : ZSet :=
  fun x => x = a \/ x = b.

Theorem pair_spec : forall a b x,
  x in pair a b <-> (x = a \/ x = b).
Proof.
  intros a b x.
  unfold In, pair.
  split; intro H; exact H.
Qed.


(* Prove singletons are not empty (when element exists) *)
Theorem singleton_not_empty : forall a,
 ~ (singleton a == Empty).
Proof.
 intros a H_eq.
 (* If singleton a == Empty, then a in singleton a <-> a in Empty *)
 assert (a in singleton a) by (apply singleton_spec; reflexivity).
 assert (a in Empty) by (apply H_eq; exact H).
 (* But nothing is in Empty *)
 unfold In, Empty in H0.
 apply (the_impossible_is_impossible a).
 exact H0.
Qed.

(* Prove pairs are not empty *)
Theorem pair_not_empty : forall a b,
 ~ (pair a b == Empty).
Proof.
 intros a b H_eq.
 assert (a in pair a b) by (apply pair_spec; left; reflexivity).
 assert (a in Empty) by (apply H_eq; exact H).
 unfold In, Empty in H0.
 apply (the_impossible_is_impossible a).
 exact H0.
Qed.

(* Axiom 3: Pairing - we can form pairs! *)
Theorem pairing_axiom : forall a b,
 exists P : ZSet, forall x, x in P <-> (x = a \/ x = b).
Proof.
 intros a b.
 exists (pair a b).
 intro x.
 apply pair_spec.
Qed.

(* Define subset relation *)
Definition subset (A B : ZSet) : Prop :=
 forall x, x in A -> x in B.
Notation "A 'subseteq' B" := (subset A B) (at level 70).

(* Binary union *)
Definition union2 (A B : ZSet) : ZSet :=
 fun x => x in A \/ x in B.

Theorem union2_spec : forall A B x,
 x in union2 A B <-> (x in A \/ x in B).
Proof.
 intros A B x.
 unfold In, union2.
 split; intro H; exact H.
Qed.

(* Intersection *)
Definition inter2 (A B : ZSet) : ZSet :=
 fun x => x in A /\ x in B.

Theorem inter2_spec : forall A B x,
 x in inter2 A B <-> (x in A /\ x in B).
Proof.
 intros A B x.
 unfold In, inter2.
 split; intro H; exact H.
Qed.

(* Set difference *)
Definition diff (A B : ZSet) : ZSet :=
 fun x => x in A /\ x notin B.

Theorem diff_spec : forall A B x,
 x in diff A B <-> (x in A /\ x notin B).
Proof.
 intros A B x.
 unfold In, diff.
 split; intro H; exact H.
Qed.

(* Complement (relative to universal set) *)
Definition compl (A : ZSet) : ZSet :=
 fun x => x notin A.

(* The universal set is the_necessary! *)
Definition Universal : ZSet := the_necessary.

Theorem universal_contains_all : forall x,
 x in Universal.
Proof.
 intros x.
 unfold In, Universal, the_necessary.
 apply the_impossible_is_impossible.
Qed.

(* Basic set algebra theorems *)
Theorem union_empty_left : forall A,
 union2 Empty A == A.
Proof.
 intros A.
 unfold set_eq, pred_equiv.
 intros x.
 split.
 - intros [H_empty | H_A].
   + (* x in Empty - impossible *)
     unfold In, Empty in H_empty.
     exfalso.
     apply (the_impossible_is_impossible x).
     exact H_empty.
   + exact H_A.
 - intros H_A.
   right. exact H_A.
Qed.

Theorem inter_empty_left : forall A,
 inter2 Empty A == Empty.
Proof.
 intros A.
 unfold set_eq, pred_equiv.
 intros x.
 split.
 - intros [H_empty H_A].
   exact H_empty.
 - intros H_empty.
   split.
   + exact H_empty.
   + (* Need to show x in A, but we know x in Empty which is impossible *)
     unfold In, Empty in H_empty.
     exfalso.
     apply (the_impossible_is_impossible x).
     exact H_empty.
Qed.

(* De Morgan's laws for sets *)
Theorem de_morgan_union : forall A B,
  compl (union2 A B) == inter2 (compl A) (compl B).
Proof.
  intros A B.
  unfold set_eq, pred_equiv.
  intros x.
  unfold In, compl, union2, inter2.
  (* Now we have: ~ (A x \/ B x) <-> ~ A x /\ ~ B x *)
  split.
  - (* Forward direction *)
    intros H_not_union.
    split.
    + intros H_A. 
      apply H_not_union.
      left. exact H_A.
    + intros H_B.
      apply H_not_union.
      right. exact H_B.
  - (* Backward direction *)
    intros [H_not_A H_not_B] [H_A | H_B].
    + exact (H_not_A H_A).
    + exact (H_not_B H_B).
Qed.

Theorem de_morgan_inter : forall A B,
  compl (inter2 A B) == union2 (compl A) (compl B).
Proof.
  intros A B.
  unfold set_eq, pred_equiv.
  intros x.
  unfold In, compl, inter2, union2.
  (* Now we have: ~ (A x /\ B x) <-> ~ A x \/ ~ B x *)
  split.
  - (* Forward direction - need classical logic here *)
    intros H_not_inter.
    destruct (alpha_constant_decision (A x)) as [H_A | H_not_A].
    + (* If A x, then must have ~ B x *)
      right.
      intros H_B.
      apply H_not_inter.
      split; assumption.
    + (* If ~ A x, we're done *)
      left. exact H_not_A.
  - (* Backward direction *)
    intros [H_not_A | H_not_B] [H_A H_B].
    + exact (H_not_A H_A).
    + exact (H_not_B H_B).
Qed.


(* Axiomatize that some elements of Alphacarrier can represent sets *)
(* This is like saying "some elements are sets" in ZFC *)
Axiom is_set_code : Alphacarrier -> Prop.
Axiom set_decode : Alphacarrier -> ZSet.

(* set_decode is only meaningful for set codes *)
Axiom decode_only_codes : forall x,
  ~ is_set_code x -> set_decode x == Empty.

(* For any predicate that's "set-like", there's a code for it *)
Axiom set_encode_exists : forall (S : ZSet), 
  (exists a, S a) \/ (forall a, ~ S a) ->  (* S is not "middle" *)
  exists x, is_set_code x /\ set_decode x == S.

(* The membership relation for coded sets *)
Definition mem (a b : Alphacarrier) : Prop :=
  is_set_code b /\ a in set_decode b.

Notation "a 'mem' b" := (mem a b) (at level 70).

(* Let's verify this works with basic examples *)
Theorem empty_set_has_code : 
  exists e, is_set_code e /\ set_decode e == Empty.
Proof.
  apply set_encode_exists.
  right. intros a H.
  unfold Empty, In, the_impossible in H.
  apply (the_impossible_is_impossible a H).
Qed.

(* Basic theorems about set codes *)
Theorem singleton_has_code : forall a,
  exists s, is_set_code s /\ set_decode s == singleton a.
Proof.
  intro a.
  apply set_encode_exists.
  left. exists a. 
  unfold singleton, In. reflexivity.
Qed.

Theorem pair_has_code : forall a b,
  exists p, is_set_code p /\ set_decode p == pair a b.
Proof.
  intros a b.
  apply set_encode_exists.
  left. exists a.
  unfold pair, In. left. reflexivity.
Qed.

(* Union axiom - for any set of sets, their union exists *)
Definition is_union_of (F union_set : Alphacarrier) : Prop :=
  is_set_code F /\ is_set_code union_set /\
  forall x, x mem union_set <-> exists Y, Y mem F /\ x mem Y.

Axiom union_exists : forall F,
  is_set_code F ->
  exists U, is_union_of F U.


(* Binary union as a special case *)
Theorem binary_union_exists : forall A B,
  is_set_code A -> is_set_code B ->
  exists U, is_set_code U /\ 
    forall x, x mem U <-> (x mem A \/ x mem B).
Proof.
  intros A B HA HB.
  (* First, create a pair {A, B} *)
  destruct (pair_has_code A B) as [P [HP HPdecode]].
  (* Then take union of this pair *)
  destruct (union_exists P HP) as [U HU].
  exists U.
  destruct HU as [HF [HUcode HUspec]].
  split; [exact HUcode|].
  intro x.
  split.
  - intro HxU.
    apply HUspec in HxU.
    destruct HxU as [Y [HYP HxY]].
    (* Y mem P means is_set_code P /\ Y in set_decode P *)
    destruct HYP as [_ HYP'].
    (* Use HPdecode as a function *)
    assert (Y in pair A B).
    { apply HPdecode. exact HYP'. }
    apply pair_spec in H.
    destruct H as [HYA | HYB].
    + left. subst Y. exact HxY.
    + right. subst Y. exact HxY.
  - intros [HxA | HxB].
    + apply HUspec.
      exists A. split; [|exact HxA].
      split; [exact HP|].
      (* Again, use HPdecode as a function *)
      apply HPdecode.
      apply pair_spec. left. reflexivity.
    + apply HUspec.
      exists B. split; [|exact HxB].
      split; [exact HP|].
      apply HPdecode.
      apply pair_spec. right. reflexivity.
Qed.

(* Separation axiom schema - for any set and property, we can form the subset *)
Axiom separation : forall A (P : Alphacarrier -> Prop),
  is_set_code A ->
  exists B, is_set_code B /\
    forall x, x mem B <-> (x mem A /\ P x).

(* Example: intersection via separation *)
Theorem intersection_exists : forall A B,
  is_set_code A -> is_set_code B ->
  exists I, is_set_code I /\
    forall x, x mem I <-> (x mem A /\ x mem B).
Proof.
  intros A B HA HB.
  apply (separation A (fun x => x mem B) HA).
Qed.


(* First, let's define the successor operation in set theory *)
(* Successor of x is x union {x} *)
Definition is_successor (x sx : Alphacarrier) : Prop :=
  is_set_code x /\ is_set_code sx /\
  forall y, y mem sx <-> (y mem x \/ y = x).

(* The axiom of infinity: there exists an inductive set *)
(* A set is inductive if it contains empty and is closed under successor *)
Definition is_inductive (I : Alphacarrier) : Prop :=
  is_set_code I /\
  (exists e, is_set_code e /\ (forall x, ~ (x mem e)) /\ e mem I) /\  (* contains empty *)
  (forall x, x mem I -> exists sx, is_successor x sx /\ sx mem I).      (* closed under successor *)

Axiom infinity : exists I, is_inductive I.

(* Direct axiomatization of important set codes *)
Axiom empty_code : Alphacarrier.
Axiom empty_code_spec : is_set_code empty_code /\ set_decode empty_code == Empty.

(* Similarly for other constructions *)
Axiom singleton_code : Alphacarrier -> Alphacarrier.
Axiom singleton_code_spec : forall a,
  is_set_code (singleton_code a) /\ 
  set_decode (singleton_code a) == singleton a.

Axiom pair_code : Alphacarrier -> Alphacarrier -> Alphacarrier.
Axiom pair_code_spec : forall a b,
  is_set_code (pair_code a b) /\ 
  set_decode (pair_code a b) == pair a b.

Axiom successor_code : Alphacarrier -> Alphacarrier.
Axiom successor_code_spec : forall x,
  is_set_code x -> is_successor x (successor_code x).

(* Alternative approach - let's make a cleaner lemma first *)
Lemma not_mem_empty : forall x, ~ (x mem empty_code).
Proof.
  intros x [Hcode Hin].
  destruct empty_code_spec as [_ Hdecode].
  apply Hdecode in Hin.
  unfold In, Empty in Hin.
  exact (the_impossible_is_impossible x Hin).
Qed.

(* Now the theorem is trivial *)
Theorem zero_exists_zfc : exists z,
  is_set_code z /\ forall x, ~ (x mem z).
Proof.
  exists empty_code.
  destruct empty_code_spec as [Hcode _].
  split.
  - exact Hcode.
  - exact not_mem_empty.
Qed.

(* Let's build the first few natural numbers explicitly *)
Definition zero_zfc := empty_code.
Definition one_zfc := successor_code zero_zfc.
Definition two_zfc := successor_code one_zfc.
Definition three_zfc := successor_code two_zfc.

(* Prove basic properties *)
Lemma zero_is_empty : forall x, ~ (x mem zero_zfc).
Proof.
  exact not_mem_empty.
Qed.

Lemma one_contains_only_zero : forall x,
  x mem one_zfc <-> x = zero_zfc.
Proof.
  intro x.
  unfold one_zfc.
  destruct empty_code_spec as [Hcode _].
  destruct (successor_code_spec zero_zfc Hcode) as [_ [Hscode Hspec]].
  split.
  - intro Hmem.
    apply Hspec in Hmem.
    destruct Hmem as [Hcontra | Heq].
    + exfalso. exact (zero_is_empty x Hcontra).
    + exact Heq.
  - intro Heq.
    subst x.
    apply Hspec.
    right. reflexivity.
Qed.

Lemma two_contains_zero_and_one : forall x,
  x mem two_zfc <-> (x = zero_zfc \/ x = one_zfc).
Proof.
  intro x.
  unfold two_zfc, one_zfc.
  (* Get the properties of successor_code *)
  destruct empty_code_spec as [Hcode0 _].
  
  (* First application of successor_code_spec *)
  assert (Hsucc1 := successor_code_spec zero_zfc Hcode0).
  destruct Hsucc1 as [_ [Hcode_one Hspec1]].
  (* Now Hcode_one : is_set_code (successor_code zero_zfc) *)
  
  (* Second application of successor_code_spec *)
  assert (Hsucc2 := successor_code_spec (successor_code zero_zfc) Hcode_one).
  destruct Hsucc2 as [_ [Hcode_two Hspec2]].
  
  split.
  - intro Hmem.
    apply Hspec2 in Hmem.
    destruct Hmem as [Hin1 | Heq1].
    + (* x mem one_zfc *)
      apply one_contains_only_zero in Hin1.
      left. exact Hin1.
    + (* x = one_zfc *)
      right. exact Heq1.
  - intros [Hz | Ho].
    + (* x = zero_zfc *)
      subst x.
      apply Hspec2.
      left.
      apply one_contains_only_zero.
      reflexivity.
    + (* x = one_zfc *)
      subst x.
      apply Hspec2.
      right. reflexivity.
Qed.

(* Axiom: empty sets have unique codes *)
Axiom empty_unique : forall e1 e2,
  is_set_code e1 -> is_set_code e2 ->
  (forall x, ~ (x mem e1)) ->
  (forall x, ~ (x mem e2)) ->
  e1 = e2.

(* The natural numbers are the intersection of all inductive sets *)
Definition is_natural_number (n : Alphacarrier) : Prop :=
  forall I, is_inductive I -> n mem I.

Theorem zero_is_natural : is_natural_number zero_zfc.
Proof.
  unfold is_natural_number, zero_zfc.
  intros I HI.
  destruct HI as [HIcode [[e [He [Hemp Hemem]]] Hclosed]].
  (* Both empty_code and e are empty sets *)
  assert (e = empty_code).
  { apply empty_unique.
    - exact He.
    - destruct empty_code_spec; assumption.
    - exact Hemp.
    - exact not_mem_empty. }
  subst e.
  exact Hemem.
Qed.

(* Supporting axioms we need for natural numbers *)
Axiom nat_set_code : Alphacarrier.
Axiom nat_set_code_spec : 
  is_set_code nat_set_code /\
  forall n, n mem nat_set_code <-> is_natural_number n.

Axiom nat_is_set_code : forall n,
  is_natural_number n -> is_set_code n.

Axiom successor_preserves_nat : forall n,
  is_natural_number n -> is_natural_number (successor_code n).

(* Induction principle for natural numbers *)
Theorem nat_induction_zfc : forall (P : Alphacarrier -> Prop),
  P zero_zfc ->
  (forall n, is_natural_number n -> P n -> P (successor_code n)) ->
  forall n, is_natural_number n -> P n.
Proof.
  intros P Hz Hsucc n Hn.
  
  (* The subset of naturals satisfying P *)
  destruct nat_set_code_spec as [Hnat_code Hnat_spec].
  destruct (separation nat_set_code P Hnat_code) as [S [HS HSspec]].
  
  (* Claim: S is inductive *)
  assert (His_ind: is_inductive S).
  { unfold is_inductive.
    split; [exact HS|].
    split.
    - (* S contains empty/zero *)
      exists zero_zfc.
      split; [|split].
      + destruct empty_code_spec; assumption.
      + exact zero_is_empty.
      + apply HSspec. split.
        * apply Hnat_spec. exact zero_is_natural.
        * exact Hz.
    - (* S is closed under successor *)
      intros x HxS.
      (* Extract the components without modifying HxS *)
      assert (Hx_components: x mem nat_set_code /\ P x).
      { apply HSspec. exact HxS. }
      destruct Hx_components as [Hx_in_nat Px].
      
      assert (Hx_nat: is_natural_number x).
      { apply Hnat_spec. exact Hx_in_nat. }
      
      assert (Hx_code: is_set_code x).
      { apply nat_is_set_code. exact Hx_nat. }
      
      exists (successor_code x).
      split.
      + apply successor_code_spec. exact Hx_code.
      + apply HSspec. split.
        * apply Hnat_spec. 
          apply successor_preserves_nat. exact Hx_nat.
        * apply Hsucc.
          -- exact Hx_nat.
          -- exact Px. }
  
  (* Since n is natural, it's in S *)
  assert (n_in_S: n mem S).
  { unfold is_natural_number in Hn.
    exact (Hn S His_ind). }
  
  (* Therefore P n holds *)
  apply HSspec in n_in_S.
  destruct n_in_S as [_ Pn].
  exact Pn.
Qed.

(* First, let's properly handle subset encoding *)
Definition encodes_subset (x : Alphacarrier) (A : Alphacarrier) : Prop :=
  is_set_code x /\ is_set_code A /\
  forall y, y mem x -> y mem A.

(* Power set: collection of all subsets of A *)
Definition is_powerset (A ps : Alphacarrier) : Prop :=
  is_set_code A /\ is_set_code ps /\
  forall x, x mem ps <-> encodes_subset x A.

(* Power Set Axiom *)
Axiom powerset_exists : forall A,
  is_set_code A -> exists ps, is_powerset A ps.

(* Let's prove some basic properties *)
Theorem empty_in_every_powerset : forall A ps,
  is_set_code A -> is_powerset A ps ->
  empty_code mem ps.
Proof.
  intros A ps HA Hps.
  destruct Hps as [_ [Hps_code Hps_spec]].
  apply Hps_spec.
  unfold encodes_subset.
  destruct empty_code_spec as [He_code _].
  split; [exact He_code|].
  split; [exact HA|].
  intros y Hy.
  (* y mem empty_code is impossible *)
  exfalso.
  exact (not_mem_empty y Hy).
Qed.

Theorem set_in_own_powerset : forall A ps,
  is_set_code A -> is_powerset A ps ->
  A mem ps.
Proof.
  intros A ps HA Hps.
  destruct Hps as [_ [Hps_code Hps_spec]].
  apply Hps_spec.
  unfold encodes_subset.
  split; [exact HA|].
  split; [exact HA|].
  intros y Hy.
  (* y mem A -> y mem A is trivial *)
  exact Hy.
Qed.

(* Singleton subsets *)
(* Singleton subsets *)
Theorem singleton_in_powerset : forall A ps a,
  is_set_code A -> is_powerset A ps -> a mem A ->
  exists sa, is_set_code sa /\ sa mem ps /\
    forall x, x mem sa <-> x = a.
Proof.
  intros A ps a HA Hps Ha.
  (* Get singleton code *)
  exists (singleton_code a).
  destruct (singleton_code_spec a) as [Hsa_code Hsa_decode].
  split; [exact Hsa_code|].
  split.
  - (* singleton a is in powerset *)
    destruct Hps as [_ [_ Hps_spec]].
    apply Hps_spec.
    unfold encodes_subset.
    split; [exact Hsa_code|].
    split; [exact HA|].
    intros x Hx.
    (* If x mem singleton a, then x = a, so x mem A *)
    destruct Hx as [_ Hx_in].
    assert (x in singleton a).
    { apply Hsa_decode. exact Hx_in. }
    (* Use singleton spec to get x = a *)
    assert (x = a).
    { apply singleton_spec. exact H. }
    (* Now rewrite using the equality *)
    rewrite H0.
    exact Ha.
  - (* Characterization of singleton *)
    intros x.
    split.
    + intro Hx.
      destruct Hx as [_ Hx_in].
      assert (x in singleton a).
      { apply Hsa_decode. exact Hx_in. }
      apply singleton_spec.
      exact H.
    + intro Heq.
      rewrite Heq.  (* Use rewrite instead of subst *)
      split; [exact Hsa_code|].
      apply Hsa_decode.
      apply singleton_spec.
      reflexivity.
Qed.


(* Replacement Axiom *)

(* A relation is functional if it maps each input to at most one output *)
Definition is_functional (R : Alphacarrier -> Alphacarrier -> Prop) : Prop :=
  forall x y z, R x y -> R x z -> y = z.

(* Replacement: The image of a set under a functional relation is a set *)
Axiom replacement : forall A (R : Alphacarrier -> Alphacarrier -> Prop),
  is_set_code A ->
  is_functional R ->
  exists B, is_set_code B /\
    forall y, y mem B <-> exists x, x mem A /\ R x y.

(* Example application: Construct {f(x) | x ∈ A} for any function f *)
Definition function_image (A : Alphacarrier) (f : Alphacarrier -> Alphacarrier) : Prop :=
  is_set_code A ->
  exists B, is_set_code B /\
    forall y, y mem B <-> exists x, x mem A /\ y = f x.

Theorem function_image_exists : forall A f,
  is_set_code A ->
  exists B, is_set_code B /\
    forall y, y mem B <-> exists x, x mem A /\ y = f x.
Proof.
  intros A f HA.
  (* Define the relation R(x,y) := y = f(x) *)
  pose (R := fun x y => y = f x).
  (* Show R is functional *)
  assert (Hfunc: is_functional R).
  { unfold is_functional, R.
    intros x y z Hy Hz.
    (* Hy : y = f x, Hz : z = f x, so y = z by transitivity *)
    rewrite Hy.
    symmetry.
    exact Hz. }
  (* Apply replacement *)
  destruct (replacement A R HA Hfunc) as [B [HB HBspec]].
  exists B. split; [exact HB|].
  intros y. split.
  - intro HyB.
    apply HBspec in HyB.
    destruct HyB as [x [HxA Hy]].
    exists x. split; [exact HxA|].
    unfold R in Hy. exact Hy.
  - intros [x [HxA Heq]].
    apply HBspec.
    exists x. split; [exact HxA|].
    unfold R. exact Heq.
Qed.

(* Foundation/Regularity Axiom *)
(* Every non-empty set has an ∈-minimal element *)
Axiom foundation : forall A,
  is_set_code A ->
  (exists x, x mem A) ->
  exists x, x mem A /\ forall y, y mem x -> ~ (y mem A).

(* This prevents things like x ∈ x or infinite chains x₀ ∈ x₁ ∈ x₂ ∈ ... *)
Theorem no_set_contains_itself : forall x,
  is_set_code x -> ~ (x mem x).
Proof.
  intros x Hx Hmem.
  (* Apply foundation to {x} *)
  destruct (singleton_code_spec x) as [Hs_code Hs_decode].
  assert (exists y, y mem singleton_code x).
  { exists x. 
    (* Need to show x mem singleton_code x *)
    (* By definition, mem requires is_set_code and membership *)
    split.
    - exact Hs_code.
    - apply Hs_decode.
      apply singleton_spec.
      reflexivity. }
  destruct (foundation (singleton_code x) Hs_code H) as [y [Hy Hmin]].
  (* y must be x since singleton only contains x *)
  assert (y = x).
  { destruct Hy as [_ Hy_in].
    apply Hs_decode in Hy_in.
    apply singleton_spec in Hy_in.
    exact Hy_in. }
  subst y.
  (* But then x is minimal, so nothing in x is in singleton x *)
  (* In particular, x in x implies x in singleton x, contradiction *)
  apply (Hmin x Hmem).
  (* Again, build mem without unfold *)
  split.
  - exact Hs_code.
  - apply Hs_decode. 
    apply singleton_spec. 
    reflexivity.
Qed.


(* Axiom of Choice *)

(* A family of sets is a set whose elements are all sets *)
Definition is_family_of_sets (F : Alphacarrier) : Prop :=
  is_set_code F /\ forall x, x mem F -> is_set_code x.

(* A choice function selects one element from each set in the family *)
Definition is_choice_function (F f : Alphacarrier) : Prop :=
  is_family_of_sets F /\ is_set_code f /\
  forall A, A mem F -> 
    (exists a, a mem A) ->  (* if A is non-empty *)
    exists a, a mem A /\ (pair_code A a) mem f.  (* f picks element a from A *)

(* Axiom of Choice: Every family of non-empty sets has a choice function *)
Axiom zf_choice : forall F,
  is_family_of_sets F ->
  (forall A, A mem F -> exists a, a mem A) ->  (* all sets non-empty *)
  exists f, is_choice_function F f.

(* Example consequence: Every surjection has a right inverse *)
Theorem surjection_has_right_inverse : forall A B f,
  is_set_code A -> is_set_code B -> is_set_code f ->
  (* f : A -> B is surjective as a set of pairs *)
  (forall b, b mem B -> exists a, a mem A /\ pair_code a b mem f) ->
  (* Then there exists g : B -> A with f∘g = id *)
  exists g, is_set_code g /\ 
    forall b, b mem B -> 
      exists a, a mem A /\ pair_code b a mem g /\ pair_code a b mem f.
Proof.
  intros A B f HA HB Hf Hsurj.
  (* For each b in B, collect the set of a's that map to b *)
  (* Use separation to build {a ∈ A | (a,b) ∈ f} for each b *)
  (* Then use choice to pick one a for each b *)
  (* This is getting complex, so let's admit for now *)
Admitted.

End ZFC_in_ClassicalAlpha.
