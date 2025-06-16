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


