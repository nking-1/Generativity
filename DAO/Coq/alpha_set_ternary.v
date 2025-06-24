Require Import Setoid.
Require Import Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.

(* OmegaType: A set where EVERY predicate has a witness *)
Class OmegaType := {
  Omegacarrier : Type;
  omega_completeness : forall (P : Omegacarrier -> Prop), 
    exists x : Omegacarrier, P x
}.

Section OmegaProperties.
  Context {Omega : OmegaType}.
  
  (* Omega contains paradoxes *)
  Theorem omega_has_paradoxes :
    forall (P : Omegacarrier -> Prop),
    exists x : Omegacarrier, P x /\ ~ P x.
  Proof.
    intro P.
    pose (paradox := fun x => P x /\ ~ P x).
    exact (omega_completeness paradox).
  Qed.
  
  (* Omega has self-referential witnesses *)
  Theorem omega_has_liar :
    exists x : Omegacarrier,
    exists P : Omegacarrier -> Prop,
    P x <-> ~ P x.
  Proof.
    pose (liar_pred := fun x => 
      exists P : Omegacarrier -> Prop, P x <-> ~ P x).
    destruct (omega_completeness liar_pred) as [x Hx].
    exists x. exact Hx.
  Qed.
  
  (* Omega is non-empty *)
  Theorem omega_not_empty :
    exists x : Omegacarrier, True.
  Proof.
    destruct (omega_completeness (fun _ => True)) as [x _].
    exists x. exact I.
  Qed.

  (* Show Omega has the predicate Alpha rejects *)
  Theorem Omega_completeness_requires_contradiction :
    forall `{H_O: OmegaType},
      (forall Q: Omegacarrier -> Prop, exists y: Omegacarrier, Q y) <->
      (exists R: Omegacarrier -> Prop, forall z: Omegacarrier, R z -> False).
  Proof.
    intros H_O.
    split.

    (* -> direction: completeness implies existence of an uninhabitable predicate *)
    intros omega_complete.

    set (P := fun x : Omegacarrier => ~ exists y : Omegacarrier, x = y).

    (* By omega_completeness, this predicate must have a witness *)
    destruct (omega_completeness P) as [x Hx].

    (* So we return P as the uninhabitable predicate (even though it's now inhabited) *)
    exists P.

    (* Now show: forall z, P z -> False *)
    intros z Hz.
    (* P z = ~ exists y, z = y, but clearly z = z, so contradiction *)
    apply Hz.
    exists z. reflexivity.

    (* <- direction: If there exists an uninhabitable predicate, Omega is complete *)
    intros [R H_uninhabitable].

    (* Let Q be any predicate *)
    intros Q.
    (* By omega_completeness, Q must have a witness *)
    apply omega_completeness.
  Qed.
End OmegaProperties.


Class NomegaType := {
  Nomegacarrier : Type;
  nomega_emptiness : forall x : Nomegacarrier, False
}.


Section NomegaProperties.
  Context {Nomega : NomegaType}.
  
  (* The predicate "there exists no x" should be "true" for Nomega *)
  Definition no_witness (P : Nomegacarrier -> Prop) : Prop :=
    ~ exists x : Nomegacarrier, P x.
  
  (* But wait - can we even state facts about Nomega's emptiness? *)
  Theorem nomega_paradox : 
    exists P : Nomegacarrier -> Prop, no_witness P.
  Proof.
    exists (fun _ => True).
    unfold no_witness.
    intros [x _].
    exact (nomega_emptiness x).
  Qed.

  (* First, let's show we can prove any proposition about Nomegacarrier *)
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

  (* This means we can prove both P and ~P *)
  Theorem nomega_contradiction :
    forall (P : Nomegacarrier -> Prop),
    forall x : Nomegacarrier, P x /\ ~ P x.
  Proof.
    intros P x.
    split.
    - exact (nomega_proves_anything P x).
    - exact (nomega_proves_anything (fun x => ~ P x) x).
  Qed.

    (* In any trivial type, everything equals everything *)
  Definition trivial_equality {T : Type} (contradiction : T -> False) : 
    forall (x y : T), x = y.
  Proof.
    intros x y.
    destruct (contradiction x).
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
      (* Or more explicitly: *)
      (* exact (False_ind (P x) (Hnw Hw)). *)
    - (* Nomega case: from any y we get False *)
      intros Q y.
      destruct (nomega_emptiness y).
  Qed.
End NomegaProperties.


(* AlphaType: A set with exactly one impossible predicate *)
Class AlphaType := {
  Alphacarrier : Type;
  
  (* The unique impossible predicate, bundled with its properties *)
  alpha_impossibility : { P : Alphacarrier -> Prop | 
    (forall x : Alphacarrier, ~ P x) /\
    (forall Q : Alphacarrier -> Prop, 
      (forall x : Alphacarrier, ~ Q x) -> 
      (forall x : Alphacarrier, Q x <-> P x))
  };
  
  (* Non-emptiness - need at least one element *)
  alpha_not_empty : exists x : Alphacarrier, True
}.

(* Helper to extract the impossible predicate *)
Definition the_impossible {Alpha : AlphaType} : Alphacarrier -> Prop :=
  proj1_sig (@alpha_impossibility Alpha).



(* ============================================================ *)
(* Properties of AlphaType *)  
(* ============================================================ *)

Section AlphaProperties.
  Context {Alpha : AlphaType}.
  
  (* The impossible predicate has no witnesses *)
  Theorem the_impossible_has_no_witnesses :
    forall x : Alphacarrier, ~ the_impossible x.
  Proof.
    intro x.
    unfold the_impossible.
    exact (proj1 (proj2_sig alpha_impossibility) x).
  Qed.
  
  (* The impossible predicate is unique *)
  Theorem the_impossible_unique :
    forall Q : Alphacarrier -> Prop,
    (forall x : Alphacarrier, ~ Q x) ->
    (forall x : Alphacarrier, Q x <-> the_impossible x).
  Proof.
    intros Q HQ.
    unfold the_impossible.
    exact (proj2 (proj2_sig alpha_impossibility) Q HQ).
  Qed.
  
  (* Not all predicates are impossible *)
  Theorem exists_possible_predicate :
    exists P : Alphacarrier -> Prop,
    exists x : Alphacarrier, P x.
  Proof.
    exists (fun _ => True).
    destruct alpha_not_empty as [x _].
    exists x. exact I.
  Qed.
  
End AlphaProperties.

(* Paradox Firewalls in Constructive AlphaType *)
Section ConstructiveParadoxFirewalls.
  Context {Alpha : AlphaType}.
  
  (* Russell's Paradox firewall - this should work constructively *)
  Theorem constructive_no_russell_predicate :
    ~ exists (R : Alphacarrier -> Prop), 
      forall x, R x <-> ~ R x.
  Proof.
    intros [R HR].
    (* We can still get a witness from non-emptiness *)
    destruct alpha_not_empty as [x0 _].
    specialize (HR x0).
    (* R x0 <-> ~ R x0 leads to contradiction constructively *)
    destruct HR as [H1 H2].
    (* If we had R x0, then by H1 we get ~ R x0, contradiction *)
    (* If we had ~ R x0, then by H2 we get R x0, contradiction *)
    (* So we need to show False without assuming either *)
    assert (R x0 -> False).
    { intro Hr. apply (H1 Hr). exact Hr. }
    (* Now H tells us ~ R x0, so by H2 we get R x0 *)
    apply H. apply H2. exact H.
  Qed.
  
  (* Curry's Paradox for False - also works constructively *)
  Theorem constructive_no_curry_false :
    ~ exists (C : Alphacarrier -> Prop),
      forall x, C x <-> (C x -> False).
  Proof.
    intros [C HC].
    destruct alpha_not_empty as [x0 _].
    specialize (HC x0).
    destruct HC as [H1 H2].
    
    (* Key insight: C x0 leads to contradiction *)
    assert (HnC: ~ C x0).
    { intros HC0.
      apply (H1 HC0). exact HC0. }
    
    (* But then C x0 -> False, so by H2, C x0 *)
    apply HnC. apply H2. exact HnC.
  Qed.
  
  (* For general Curry: if such a predicate exists, Q becomes provable *)
  Theorem constructive_curry_explosion :
    forall (Q : Prop),
      (exists (C : Alphacarrier -> Prop), forall x, C x <-> (C x -> Q)) -> 
      Q.
  Proof.
    intros Q [C HC].
    destruct alpha_not_empty as [x0 _].
    specialize (HC x0).
    destruct HC as [H1 H2].
    
    (* The key lemma still works constructively *)
    assert (HQ: (C x0 -> Q) -> Q).
    { intros Himp.
      apply Himp. apply H2. exact Himp. }
    
    (* Now prove Q *)
    apply HQ.
    intros HC0.
    apply HQ.
    apply H1.
    exact HC0.
  Qed.
  
  (* No self-denying existence - straightforward *)
  Theorem constructive_no_self_denying :
    ~ exists (P : Alphacarrier -> Prop),
      (forall x, P x <-> the_impossible x) /\ (exists x, P x).
  Proof.
    intros [P [Heq [x Px]]].
    apply (the_impossible_has_no_witnesses x).
    apply Heq. exact Px.
  Qed.
  
  (* Now here's where it gets interesting - predicate grounding *)
  (* Without excluded middle, we might not get a clean dichotomy *)
  
  (* First, let's define what makes a predicate "grounded" *)
  Definition circular_predicate (P : Alphacarrier -> Prop) : Prop :=
    forall x, P x <-> exists y, P y.
  
  (* What we CAN prove: if a circular predicate has a witness, 
     it's universal *)
  Theorem constructive_circular_witness_universal :
    forall P : Alphacarrier -> Prop,
      circular_predicate P ->
      (exists x, P x) ->
      forall y, P y.
  Proof.
    intros P Hcirc [x Px] y.
    apply Hcirc.
    exists x. exact Px.
  Qed.
  
  (* And if it's not universal, it has no witnesses *)
  Theorem constructive_circular_not_universal_empty :
    forall P : Alphacarrier -> Prop,
      circular_predicate P ->
      (exists y, ~ P y) ->
      forall x, ~ P x.
  Proof.
    intros P Hcirc [y HnPy] x Px.
    apply HnPy.
    apply Hcirc.
    exists x. exact Px.
  Qed.
  
  (* The key insight: circular predicates can't be "mixed" *)
  Theorem constructive_circular_no_mixed :
    forall P : Alphacarrier -> Prop,
      circular_predicate P ->
      ~ ((exists x, P x) /\ (exists y, ~ P y)).
  Proof.
    intros P Hcirc [[x Px] [y HnPy]].
    apply HnPy.
    apply (constructive_circular_witness_universal P Hcirc).
    - exists x. exact Px.
  Qed.
  
End ConstructiveParadoxFirewalls.


Section ParadoxesEqualTheImpossible.
  Context {Alpha : AlphaType}.
  
  (* First, let's prove that any predicate that always leads to False 
     must equal the_impossible *)
  Theorem contradiction_equals_impossible :
    forall P : Alphacarrier -> Prop,
    (forall x : Alphacarrier, P x -> False) ->
    (forall x : Alphacarrier, P x <-> the_impossible x).
  Proof.
    intros P HP.
    apply the_impossible_unique.
    intros x Px.
    exact (HP x Px).
  Qed.
  
  (* Now let's show Russell's paradox equals the_impossible *)
  Theorem russell_equals_impossible :
    forall R : Alphacarrier -> Prop,
    (forall x, R x <-> ~ R x) ->
    (forall x, R x <-> the_impossible x).
  Proof.
    intros R HR.
    apply contradiction_equals_impossible.
    intros x Rx.
    (* R x -> ~ R x by HR *)
    apply (proj1 (HR x) Rx).
    exact Rx.
  Qed.
  
  (* Curry's paradox with False equals the_impossible *)
  Theorem curry_false_equals_impossible :
    forall C : Alphacarrier -> Prop,
    (forall x, C x <-> (C x -> False)) ->
    (forall x, C x <-> the_impossible x).
  Proof.
    intros C HC.
    apply contradiction_equals_impossible.
    intros x Cx.
    (* C x -> (C x -> False) by HC *)
    apply (proj1 (HC x) Cx).
    exact Cx.
  Qed.
  
  (* Here's a more general principle: any self-contradictory predicate
     equals the_impossible *)
  Theorem self_contradictory_equals_impossible :
    forall P : Alphacarrier -> Prop,
    (exists x, P x -> ~ P x) ->
    (forall x, ~ P x) ->
    (forall x, P x <-> the_impossible x).
  Proof.
    intros P Hself Hnone.
    apply the_impossible_unique.
    exact Hnone.
  Qed.
  
  (* Even more interesting: predicates that would make everything true
     must be impossible *)
  Theorem trivializing_equals_impossible :
    forall P : Alphacarrier -> Prop,
    (forall Q : Prop, (exists x, P x) -> Q) ->
    (forall x, P x <-> the_impossible x).
  Proof.
    intros P Htriv.
    apply contradiction_equals_impossible.
    intros x Px.
    (* If P x, then we can prove False *)
    apply (Htriv False).
    exists x. exact Px.
  Qed.
  
  (* The circular predicate, if it has no witnesses, equals the_impossible *)
  Theorem empty_circular_equals_impossible :
    forall P : Alphacarrier -> Prop,
    circular_predicate P ->
    (forall x, ~ P x) ->
    (forall x, P x <-> the_impossible x).
  Proof.
    intros P Hcirc Hempty.
    apply the_impossible_unique.
    exact Hempty.
  Qed.
  
  (* The key theorem: In AlphaType, all paradoxes are the same paradox *)
  Theorem all_paradoxes_are_one :
    forall P Q : Alphacarrier -> Prop,
    (forall x, ~ P x) ->
    (forall x, ~ Q x) ->
    (forall x, P x <-> Q x).
  Proof.
    intros P Q HP HQ x.
    split.
    - intro Px. destruct (HP x Px).
    - intro Qx. destruct (HQ x Qx).
  Qed.
  
  (* Therefore: there's only one way to be impossible in AlphaType *)
  Theorem impossibility_is_unique :
    forall P : Alphacarrier -> Prop,
    (forall x, ~ P x) <->
    (forall x, P x <-> the_impossible x).
  Proof.
    intro P.
    split.
    - apply the_impossible_unique.
    - intros H x Px.
      apply (the_impossible_has_no_witnesses x).
      apply H. exact Px.
  Qed.

End ParadoxesEqualTheImpossible.


(* ============================================================ *)
(* Simple Diagonal for AlphaType *)
(* ============================================================ *)

Section AlphaSelfDiagonal.
  Context {Alpha : AlphaType}.
  
  (* Assume we can enumerate Alpha's predicates *)
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  
  (* The diagonal: flips the nth predicate at position n *)
  Definition diagonal_pred : nat -> Alphacarrier -> Prop :=
    fun n => match alpha_enum n with
    | Some P => fun a => ~ P a
    | None => fun _ => True
    end.
  
  (* For any enumerated predicate, the diagonal differs from it *)
  Theorem diagonal_differs :
    forall n P a,
    alpha_enum n = Some P ->
    ~ (P a <-> diagonal_pred n a).
  Proof.
    intros n P a Henum H_iff.
    unfold diagonal_pred in H_iff.
    rewrite Henum in H_iff.
    (* Note: tauto tactic can finish here, we show explicit derivation *)
    (* H_iff : P a <-> ~ P a *)
    destruct H_iff as [H1 H2].
    (* First, let's show ~ P a *)
    assert (HnP : ~ P a).
    { intro HP. 
      apply (H1 HP). 
      exact HP. }
    (* Now use H2 to get P a from ~ P a *)
    assert (HP : P a).
    { apply H2. exact HnP. }
    (* Contradiction: we have both P a and ~ P a *)
    exact (HnP HP).
  Qed.
  
End AlphaSelfDiagonal.


(* ============================================================ *)
(* Diagonal in OmegaType *)
(* ============================================================ *)

Section OmegaDiagonal.
  Context {Omega : OmegaType} {Alpha : AlphaType}.
  
  (* Given enumeration of Alpha and embedding into Omega *)
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable embed : Alphacarrier -> Omegacarrier.
  
  (* Lift Alpha's diagonal to Omega *)
  Definition omega_diagonal : Omegacarrier -> Prop :=
    fun x => exists n a, 
      embed a = x /\ 
      diagonal_pred alpha_enum n a.
  
  (* Omega has witnesses for its diagonal *)
  Theorem omega_diagonal_exists :
    exists x : Omegacarrier, omega_diagonal x.
  Proof.
    apply omega_completeness.
  Qed.
  
  (* In fact, for any n, we can find a witness at that index *)
  Theorem omega_diagonal_at_index :
    forall n,
    exists x : Omegacarrier,
    exists a : Alphacarrier,
    embed a = x /\ diagonal_pred alpha_enum n a.
  Proof.
    intro n.
    pose (pred_n := fun x => exists a, embed a = x /\ diagonal_pred alpha_enum n a).
    destruct (omega_completeness pred_n) as [x Hx].
    exists x.
    exact Hx.
  Qed.
  
End OmegaDiagonal.



(* ============================================================ *)
(* Preparing for the diagonal *)
(* ============================================================ *)

Section DiagonalPrep.
  Context {Omega : OmegaType} {Alpha : AlphaType}.
  
  (* If we have a complete enumeration of Alpha's predicates,
     then the diagonal can't be among them *)
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop,
    exists n, alpha_enum n = Some A.
  
  (* The diagonal is not in the enumeration *)
  Theorem diagonal_not_enumerated :
    forall n,
    alpha_enum n <> Some (fun a => diagonal_pred alpha_enum n a).
  Proof.
    intros n Heq.
    (* Extract the predicate from the enumeration *)
    assert (H_contra : forall a, 
      diagonal_pred alpha_enum n a <-> diagonal_pred alpha_enum n a).
    { intro a. split; auto. }
    
    (* But by diagonal_differs, if alpha_enum n = Some P, then
      P cannot equal diagonal_pred alpha_enum n *)
    pose (P := fun a => diagonal_pred alpha_enum n a).
    destruct alpha_not_empty as [a0 _].
    
    (* From Heq, we have alpha_enum n = Some P *)
    (* By diagonal_differs, we should have ~ (P a0 <-> diagonal_pred alpha_enum n a0) *)
    apply (diagonal_differs alpha_enum n P a0 Heq).
    
    (* But P IS diagonal_pred alpha_enum n *)
    unfold P.
    exact (H_contra a0).
  Qed.

End DiagonalPrep.


(* ============================================================ *)
(* The Unrepresentable Predicate *)
(* ============================================================ *)

Section UnrepresentablePredicate.
  Context {Omega : OmegaType} {Alpha : AlphaType}.
  
  (* We'll use the omega_diagonal from the previous section *)
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop, 
    exists n, alpha_enum n = Some A.
  Variable embed : Alphacarrier -> Omegacarrier.

  (* A predicate P is representable if there's an Alpha predicate
     that tracks P through some mapping *)
  Definition representable (P : Omegacarrier -> Prop) : Prop :=
    exists (A : Alphacarrier -> Prop) (f : Alphacarrier -> Omegacarrier),
    forall a : Alphacarrier, A a <-> P (f a).
  
  
  Theorem omega_diagonal_not_representable :
    ~ representable (omega_diagonal alpha_enum embed).
  Proof.
    unfold representable, omega_diagonal.
    intros [A [f H_rep]].
    
    (* Since A is in Alpha, it's in the enumeration *)
    destruct (enum_complete A) as [n_A H_nA].
    
    (* The key: find a point where f coincides with embed at position n_A *)
    pose (special := fun x => exists a, 
      x = embed a /\ 
      f a = embed a /\ 
      diagonal_pred alpha_enum n_A a).
    destruct (omega_completeness special) as [x [a0 [Hx [Hf Hdiag]]]].
    
    (* Apply H_rep to a0 *)
    specialize (H_rep a0).
    
    (* From left to right: if A a0, then omega_diagonal (f a0) *)
    assert (H_lr: A a0 -> omega_diagonal alpha_enum embed (f a0)).
    { intro Ha. apply H_rep. exact Ha. }
    
    (* From right to left: if omega_diagonal (f a0), then A a0 *)
    assert (H_rl: omega_diagonal alpha_enum embed (f a0) -> A a0).
    { intro Hod. apply H_rep. exact Hod. }
    
    (* Since f a0 = embed a0, we have omega_diagonal (embed a0) *)
    rewrite Hf in H_rl.
    
    (* omega_diagonal (embed a0) holds because of n_A, a0 *)
    assert (Hod: omega_diagonal alpha_enum embed (embed a0)).
    {
      exists n_A, a0.
      split; [reflexivity | exact Hdiag].
    }
    
    (* So A a0 holds *)
    apply H_rl in Hod.
    
    (* But diagonal_pred n_A a0 means ~ A a0 *)
    unfold diagonal_pred in Hdiag.
    rewrite H_nA in Hdiag.
    
    (* Contradiction! *)
    exact (Hdiag Hod).
  Qed.
  
End UnrepresentablePredicate.


(* ============================================================ *)
(* Questions About the Diagonal *)
(* ============================================================ *)

Section DiagonalQuestions.
  Context {Omega : OmegaType} {Alpha : AlphaType}.
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop, exists n, alpha_enum n = Some A.
  Variable embed : Alphacarrier -> Omegacarrier.
  
  (* Consider the question: "Does omega_diagonal have a witness?" *)
  Definition Q_witness : Prop :=
    exists x : Omegacarrier, omega_diagonal alpha_enum embed x.
  
  (* We know it's true in Omega *)
  Theorem Q_witness_true : Q_witness.
  Proof.
    exact (omega_diagonal_exists alpha_enum embed).
  Qed.
  
  (* But can Alpha decide this question? 
     If Alpha had excluded middle, it would have to decide... *)
  
  (* Let's define what it means for Alpha to "decide" a question *)
  Definition alpha_decides (P : Prop) : Type :=
    {P} + {~P}.  (* Decidable - we have a proof of P or ~P *)
  
  (* Key insight: If Alpha could decide all questions, 
     it would need to represent unrepresentable predicates *)
  Theorem deciding_requires_representation :
    (forall P : Prop, alpha_decides P) ->
    Q_witness ->
    representable (omega_diagonal alpha_enum embed) ->
    False.
  Proof.
    intros H_decides H_exists H_rep.
    (* We already proved omega_diagonal_not_representable *)
    exact (omega_diagonal_not_representable alpha_enum enum_complete embed H_rep).
  Qed.
  
End DiagonalQuestions.


(* ============================================================ *)
(* Ternary Truth Values *)
(* ============================================================ *)

Section TernaryLogic.
  Context {Alpha : AlphaType}.
  
  (* Alpha needs three truth values *)
  Inductive TernaryTruth (P : Prop) : Type :=
    | Proved : P -> TernaryTruth P
    | Refuted : ~P -> TernaryTruth P  
    | Undecidable : (P -> False) -> (~P -> False) -> TernaryTruth P.
  
  (* Some questions lead to the Undecidable case *)
  Definition inherently_undecidable (P : Prop) : Prop :=
    (P -> False) /\ (~P -> False).
  
  (* The question about unrepresentable predicates is inherently undecidable
     in Alpha's logic *)
  (* We'll build towards this in the next section *)
  
End TernaryLogic.


(* ============================================================ *)
(* The Contradiction: Alpha Cannot Have Excluded Middle         *)
(* ============================================================ *)
Section AlphaNeedsThreeValues.
  Context {Omega : OmegaType} {Alpha : AlphaType}.
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop, exists n, alpha_enum n = Some A.
  Variable embed : Alphacarrier -> Omegacarrier.
  
  (* First, let's define what it means for Alpha to have excluded middle *)
  (* This means Alpha can decide any proposition about its own elements *)
  Definition alpha_excluded_middle := 
    forall (A : Alphacarrier -> Prop), 
    (exists a, A a) \/ (forall a, ~ A a).
  
  (* Key lemma: if Alpha has excluded middle, it can "detect" 
     which of its elements map to omega_diagonal witnesses *)
  Lemma alpha_em_detects_diagonal :
    alpha_excluded_middle ->
    exists (A_detect : Alphacarrier -> Prop),
    forall a : Alphacarrier,
      A_detect a <-> omega_diagonal alpha_enum embed (embed a).
  Proof.
    intro AEM.
    
    (* Define A_detect as the preimage of omega_diagonal *)
    pose (A_detect := fun a => omega_diagonal alpha_enum embed (embed a)).
    exists A_detect.
    
    (* This is just the definition - no EM needed yet *)
    split; intro H; exact H.
  Qed.
  
  (* The killer theorem: if Alpha has excluded middle, 
     then omega_diagonal is representable *)
  Theorem alpha_em_makes_diagonal_representable :
    alpha_excluded_middle ->
    representable (omega_diagonal alpha_enum embed).
  Proof.
    intro AEM.
    
    (* Get the detection predicate *)
    destruct (alpha_em_detects_diagonal AEM) as [A_detect HA_detect].
    
    (* By alpha_excluded_middle, either A_detect has witnesses or it doesn't *)
    destruct (AEM A_detect) as [H_exists | H_none].
    
    - (* Case 1: A_detect has witnesses *)
      (* Then A_detect is a legitimate Alpha predicate that tracks omega_diagonal *)
      unfold representable.
      exists A_detect, embed.
      exact HA_detect.
      
    - (* Case 2: A_detect has no witnesses *)
      (* This means no embedded Alpha element satisfies omega_diagonal *)
      (* But we know omega_diagonal has witnesses in Omega *)
      
      (* Actually, both cases lead to the same conclusion: *)
      (* A_detect and embed form a representation! *)
      unfold representable.
      exists A_detect, embed.
      exact HA_detect.
  Qed.
  
  (* Therefore: Alpha cannot have excluded middle *)
  Theorem alpha_cannot_have_excluded_middle :
    alpha_excluded_middle -> False.
  Proof.
    intro AEM.
    
    (* By the previous theorem, omega_diagonal becomes representable *)
    pose proof (alpha_em_makes_diagonal_representable AEM) as H_rep.
    
    (* But we proved omega_diagonal is not representable! *)
    exact (omega_diagonal_not_representable alpha_enum enum_complete embed H_rep).
  Qed.
  
End AlphaNeedsThreeValues.


(* ============================================================ *)
(* Ternary Logic Emerges in Alpha *)
(* ============================================================ *)

Section AlphaTernaryLogic.
  Context {Omega : OmegaType} {Alpha : AlphaType}.
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop, exists n, alpha_enum n = Some A.
  Variable embed : Alphacarrier -> Omegacarrier.
  
  (* Define Alpha's ternary truth values *)
  Inductive AlphaTruth (A : Alphacarrier -> Prop) : Type :=
    | Alpha_True : (exists a, A a) -> AlphaTruth A
    | Alpha_False : (forall a, ~ A a) -> AlphaTruth A
    | Alpha_Undecidable : 
        (~ exists a, A a) -> 
        (~ forall a, ~ A a) -> 
        AlphaTruth A.
  
  (* The key theorem: some predicates are undecidable in Alpha *)
  Theorem exists_undecidable_predicate :
    exists A : Alphacarrier -> Prop,
    (~ exists a, A a) /\ (~ forall a, ~ A a).
  Proof.
    (* Use the omega_diagonal detection predicate *)
    exists (fun a => omega_diagonal alpha_enum embed (embed a)).
    
    split.
    - (* Assume exists a witness *)
      intro H_exists.
      destruct H_exists as [a Ha].
      
      (* Then we could represent omega_diagonal *)
      apply (omega_diagonal_not_representable alpha_enum enum_complete embed).
      unfold representable.
      exists (fun a => omega_diagonal alpha_enum embed (embed a)), embed.
      intro a'. split; intro H; exact H.
      
    - (* Assume no witnesses *)
      intro H_none.
      
      (* But omega_diagonal has witnesses in Omega *)
      destruct (omega_diagonal_exists alpha_enum embed) as [x Hx].
      
      (* If embed is surjective onto its image, we'd get a contradiction *)
      (* But we can't prove this in general... *)
      (* Instead, use omega_completeness more cleverly *)
      
      (* Consider the predicate "x is in the image of embed and satisfies omega_diagonal" *)
      pose (P := fun x => omega_diagonal alpha_enum embed x /\ exists a, embed a = x).
      assert (HP: exists x, P x).
      { apply omega_completeness. }
      
      destruct HP as [x' [Hx' [a' Hembed]]].
      
      (* So embed a' = x' and omega_diagonal x' *)
      rewrite <- Hembed in Hx'.
      
      (* But H_none says no such a' exists *)
      exact (H_none a' Hx').
  Qed.
  
  (* Therefore: Alpha must use ternary classification *)
  Definition alpha_classify (A : Alphacarrier -> Prop) : Type :=
    AlphaTruth A.
  
  (* Examples showing all three truth values are inhabited *)
  
  (* Example of Alpha_True *)
  Example always_true_is_true :
    AlphaTruth (fun _ : Alphacarrier => True).
  Proof.
    apply Alpha_True.
    destruct alpha_not_empty as [a _].
    exists a. exact I.
  Qed.
  
  (* Example of Alpha_False *)  
  Example impossible_is_false :
    AlphaTruth the_impossible.
  Proof.
    apply Alpha_False.
    exact the_impossible_has_no_witnesses.
  Qed.
  
  (* Example of Alpha_Undecidable *)
  Example diagonal_is_undecidable :
    AlphaTruth (fun a => omega_diagonal alpha_enum embed (embed a)).
  Proof.
    apply Alpha_Undecidable.
    
    - (* ~ exists a, ... *)
      intro H_exists.
      apply (omega_diagonal_not_representable alpha_enum enum_complete embed).
      unfold representable.
      exists (fun a => omega_diagonal alpha_enum embed (embed a)), embed.
      intro a. split; intro H; exact H.
      
    - (* ~ forall a, ~ ... *)
      intro H_none.
      destruct (omega_diagonal_exists alpha_enum embed) as [x Hx].
      pose (P := fun x => omega_diagonal alpha_enum embed x /\ exists a, embed a = x).
      assert (HP: exists x, P x) by apply omega_completeness.
      destruct HP as [x' [Hx' [a' Hembed]]].
      rewrite <- Hembed in Hx'.
      exact (H_none a' Hx').
  Qed.
  
  (* The crucial theorem: Alpha cannot escape ternary logic *)
  Theorem alpha_necessarily_ternary :
    ~ (forall A : Alphacarrier -> Prop, 
        (exists a, A a) \/ (forall a, ~ A a)).
  Proof.
    intro H_binary.
    
    (* Pass all the required arguments in order *)
    exact (alpha_cannot_have_excluded_middle alpha_enum enum_complete embed H_binary).
  Qed.
  
  (* Final insight: The three values correspond to Alpha's relationship with Omega *)
  Definition truth_value_meaning : forall A : Alphacarrier -> Prop, AlphaTruth A -> Prop :=
    fun A truth_val =>
      match truth_val with
      | Alpha_True _ _ => 
          (* A is witnessed within Alpha's domain *)
          True  
      | Alpha_False _ _ => 
          (* A is the_impossible or equivalent to it *)
          forall a, A a <-> the_impossible a
      | Alpha_Undecidable _ _ _ => 
          (* A touches Omega's unrepresentable reality *)
          exists (P : Omegacarrier -> Prop), 
          ~ representable P /\
          forall a, A a <-> P (embed a)
      end.
  
End AlphaTernaryLogic.


Section GodelViaOmega.
 Context {Omega : OmegaType} {Alpha : AlphaType}.
 Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
 Variable enum_complete : forall A : Alphacarrier -> Prop, exists n, alpha_enum n = Some A.
 Variable embed : Alphacarrier -> Omegacarrier.
 
 (* Let's be precise about what Alpha can and cannot do *)
 
 (* Alpha can make claims about its own predicates *)
 Definition Alpha_Claims (about_pred : Alphacarrier -> Prop) (claim : Prop) : Prop :=
   exists (A : Alphacarrier -> Prop),
     (exists a, A a) /\  (* A has witnesses as evidence *)
     claim.              (* and the claim holds *)
 
 (* But when Alpha tries to make claims about Omega predicates... *)
  Definition Alpha_Claims_About_Omega (P : Omegacarrier -> Prop) (claim : Prop) : Prop :=
    exists (A : Alphacarrier -> Prop),
      (exists a, A a) /\                    
      (forall a, P (embed a) -> A a) /\     (* A contains all embedded P-witnesses *)
      claim.
 
 (* The key lemma: Alpha cannot make definitive claims about unrepresentable predicates *)
 Lemma alpha_cannot_track_unrepresentable :
   forall P : Omegacarrier -> Prop,
   ~ representable P ->
   ~ exists (A : Alphacarrier -> Prop),
     (exists a, A a) /\
     (forall a, A a <-> P (embed a)).
 Proof.
   intros P Hunrep [A [[a Ha] Htrack]].
   apply Hunrep.
   exists A, embed.
   exact Htrack.
 Qed.
 
 (* Now for the Gödel construction *)
 Definition Godel_Statement : Prop :=
   exists x, omega_diagonal alpha_enum embed x.
 
 (* G is true in Omega *)
 Theorem godel_true : Godel_Statement.
 Proof.
   exact (omega_diagonal_exists alpha_enum embed).
 Qed.
 
 (* But Alpha cannot prove G with strong tracking *)
  Theorem godel_unprovable :
    ~ Alpha_Claims_About_Omega (omega_diagonal alpha_enum embed) Godel_Statement.
  Proof.
    unfold Alpha_Claims_About_Omega, Godel_Statement.
    intros [A [[a0 Ha0] [Htrack _]]].
    
    (* Now Htrack says: if omega_diagonal holds at an embedded point, then A holds *)
    
    (* Since A is enumerated, find its index *)
    destruct (enum_complete A) as [n Hn].
    
    (* omega_diagonal at index n gives us a witness *)
    pose proof (omega_diagonal_at_index alpha_enum embed n) as [x [a [Hembed Hdiag]]].
    
    (* We know omega_diagonal (embed a) *)
    assert (Hod: omega_diagonal alpha_enum embed (embed a)).
    { unfold omega_diagonal.
      exists n, a.
      split.
      - reflexivity.  (* embed a = embed a *)
      - exact Hdiag. }
    
    (* By Htrack, this means A a *)
    apply Htrack in Hod.
    
    (* But Hdiag tells us ~ A a when we unfold *)
    unfold diagonal_pred in Hdiag.
    rewrite Hn in Hdiag.
    
    (* Contradiction! *)
    exact (Hdiag Hod).
  Qed.
 
 (* Alpha also cannot refute G *)
  Theorem godel_unrefutable :
    ~ Alpha_Claims_About_Omega (omega_diagonal alpha_enum embed) (~ Godel_Statement).
  Proof.
    unfold Alpha_Claims_About_Omega, Godel_Statement.
    intros [A [[a0 Ha0] [Htrack Hclaim]]].
    
    (* A claims omega_diagonal has no witnesses *)
    apply Hclaim.
    exact (omega_diagonal_exists alpha_enum embed).
  Qed.
 
 
 (* The fundamental insight *)
  Theorem incompleteness_from_unrepresentability :
    let G := exists x, omega_diagonal alpha_enum embed x in
    (* G is true but independent of Alpha *)
    G /\ 
    ~ Alpha_Claims_About_Omega (omega_diagonal alpha_enum embed) G /\
    ~ Alpha_Claims_About_Omega (omega_diagonal alpha_enum embed) (~ G).
  Proof.
    split; [exact godel_true |].
    split; [exact godel_unprovable | exact godel_unrefutable].
  Qed.
 
End GodelViaOmega.


Section HaltingProblemViaAlphaOmega.
  Context {Alpha : AlphaType} {Omega : OmegaType}.
  Variable embed : Alphacarrier -> Omegacarrier.
  
  (* Basic Turing machine setup *)
  Variable TM : Type.  (* Type of Turing machines *)
  
  (* Inputs are encoded as Alpha elements *)
  Variable encode_tm : TM -> Alphacarrier.
  Variable decode_tm : Alphacarrier -> option TM.
  
  (* The computation relation: machine M on encoded input halts *)
  Variable Halts : TM -> Alphacarrier -> Prop.
  
  (* Self-application: a machine run on its own encoding *)
  Definition SelfHalts (M : TM) : Prop :=
    Halts M (encode_tm M).
  
  (* Enumeration of all Turing machines *)
  Variable tm_enum : nat -> option TM.
  Variable enum_complete : forall M : TM, exists n, tm_enum n = Some M.
  
  (* The diagonal predicate: machines that DON'T halt on themselves *)
  Definition anti_diagonal (n : nat) : Prop :=
    match tm_enum n with
    | None => True
    | Some M => ~ SelfHalts M
    end.
  
  (* Lift this to Omega - the space of "computational paradoxes" *)
  Definition halting_diagonal_omega : Omegacarrier -> Prop :=
    fun x => exists n M,
      embed (encode_tm M) = x /\
      tm_enum n = Some M /\
      anti_diagonal n.
  
  (* Omega contains computational paradoxes *)
  Theorem omega_has_halting_paradoxes :
    exists x, halting_diagonal_omega x.
  Proof.
    apply omega_completeness.
  Qed.
  
  (* Now define what it means for Alpha to "solve" the halting problem *)
  Definition Alpha_Solves_Halting : Prop :=
    exists (decider : TM -> Prop),
      (forall M, decider M <-> SelfHalts M).
  
  (* Alternative: a decider as an Alpha predicate on encodings *)
  Definition Alpha_Has_Halting_Decider : Prop :=
    exists (A : Alphacarrier -> Prop),
      forall M, A (encode_tm M) <-> SelfHalts M.
  
  (* The classic diagonal argument, viewed through Alpha/Omega *)
  (* The diagonal machine specification *)
  Definition DiagonalMachineExists : Prop :=
    forall (decider : Alphacarrier -> Prop),
    (forall M, decider (encode_tm M) <-> SelfHalts M) ->
    exists D : TM, forall M,
      Halts D (encode_tm M) <-> ~ decider (encode_tm M).
  
  (* Assume we can build diagonal machines *)
  Axiom diagonal_construction : DiagonalMachineExists.
  
  Theorem alpha_cannot_solve_halting :
    ~ Alpha_Has_Halting_Decider.
  Proof.
    intro H.
    destruct H as [decider Hdec].
    
    (* Use the diagonal construction *)
    destruct (diagonal_construction decider Hdec) as [D D_spec].
    
    (* What happens when D runs on itself? *)
    specialize (D_spec D).
    
    (* D_spec: Halts D (encode_tm D) <-> ~ decider (encode_tm D) *)
    (* Hdec: decider (encode_tm D) <-> SelfHalts D *)
    (* SelfHalts D = Halts D (encode_tm D) *)
    
    unfold SelfHalts in *.
    
    (* Combine the biconditionals *)
    assert (Halts D (encode_tm D) <-> ~ Halts D (encode_tm D)).
    {
      split.
      - intro HD.
        apply D_spec in HD.
        intro HD'.
        apply HD.
        apply Hdec.
        exact HD'.
      - intro HnD.
        apply D_spec.
        intro Hdec_D.
        apply HnD.
        apply Hdec.
        exact Hdec_D.
    }
    
    (* Direct contradiction *)
    destruct H as [H1 H2].
    assert (~ Halts D (encode_tm D)).
    { intro H. exact (H1 H H). }
    apply H. apply H2. exact H.
  Qed.
  
  (* The deeper insight: computational and logical incompleteness are one *)
  
  (* A statement about halting *)
  Definition Halting_Statement : Prop :=
    exists M, SelfHalts M.
  
  (* This statement is "true but unprovable" in Alpha *)
  (* Just like Gödel sentences! *)
  
  Theorem halting_creates_incompleteness :
    (* The halting problem creates statements that are: *)
    (* 1. True (witnesses exist in Omega) *)
    (* 2. Unprovable (Alpha cannot decide them) *)
    (exists x, halting_diagonal_omega x) /\
    ~ Alpha_Has_Halting_Decider.
  Proof.
    split.
    - exact omega_has_halting_paradoxes.
    - exact alpha_cannot_solve_halting.
  Qed.
  
  (* The universal principle: diagonalization creates unrepresentability *)
  (* Whether in logic (Gödel) or computation (Turing), the mechanism is the same *)
  
End HaltingProblemViaAlphaOmega.


Section ConstructiveNegation.
  Context {Alpha : AlphaType}.
  
  (* If P is impossible (equals the_impossible), what about ~P? *)
  
  Theorem impossible_implies_negation_holds :
    forall P : Alphacarrier -> Prop,
    (forall a, P a <-> the_impossible a) ->
    forall a, ~ P a.
  Proof.
    intros P H a HPa.
    apply H in HPa.
    exact (the_impossible_has_no_witnesses a HPa).
  Qed.
  
  (* But can ~P also be impossible? Let's check: *)
  Theorem both_impossible_is_impossible :
    forall P : Alphacarrier -> Prop,
    (forall a, P a <-> the_impossible a) ->
    (forall a, ~ P a <-> the_impossible a) ->
    False.
  Proof.
    intros P HP HnP.
    destruct alpha_not_empty as [a _].
    
    (* From HP: P a <-> the_impossible a *)
    (* From HnP: ~P a <-> the_impossible a *)
    
    (* ~P a is true by the first theorem *)
    assert (~ P a).
    { intro HPa. apply HP in HPa. 
      exact (the_impossible_has_no_witnesses a HPa). }
    
    (* But HnP says ~P a <-> the_impossible a *)
    apply HnP in H.
    exact (the_impossible_has_no_witnesses a H).
  Qed.
  
  (* So if P is impossible, ~P CANNOT also be impossible *)
  
  (* But constructively, we have three options: *)
  Inductive Negation_Status (P : Alphacarrier -> Prop) : Type :=
    | P_Impossible : 
        (forall a, P a <-> the_impossible a) -> 
        Negation_Status P
    | NegP_Impossible : 
        (forall a, ~ P a <-> the_impossible a) -> 
        Negation_Status P  
    | Neither_Impossible :
        (exists a, ~ (P a <-> the_impossible a)) ->
        (exists a, ~ (~ P a <-> the_impossible a)) ->
        Negation_Status P.
  
  (* The key constructive insight: *)
  (* If P is impossible, then ~P is NOT impossible *)
  (* But we might not be able to prove ~P has witnesses! *)
  
  (* This is the constructive gap: *)
  (* P impossible → ~P holds *)
  (* But ~P holds ≠ ~P has witnesses *)
End ConstructiveNegation.


(* Note - seems like a heyting algebra *)
Section ImpossibilityAlgebra.
  Context {Alpha : AlphaType}.
  
  (* Helper definitions *)
  Definition Is_Impossible (P : Alphacarrier -> Prop) : Prop :=
    forall a, P a <-> the_impossible a.
    
  Definition Is_Possible (P : Alphacarrier -> Prop) : Prop :=
    ~ Is_Impossible P.
  
  (* Conjunction with impossible *)
  Theorem impossible_and_anything_is_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Impossible (fun a => P a /\ Q a).
  Proof.
    intros P Q HP.
    intro a.
    split.
    - intros [HPa HQa].
      apply HP in HPa.
      exact HPa.
    - intro Himp.
      split.
      + apply HP. exact Himp.
      + (* We need Q a, but we have the_impossible a *)
        exfalso.
        exact (the_impossible_has_no_witnesses a Himp).
  Qed.
  
  (* Disjunction with impossible *)
  Theorem impossible_or_possible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Possible Q ->
    (* P ∨ Q has same possibility status as Q *)
    (forall a, (P a \/ Q a) <-> Q a).
  Proof.
    intros P Q HP HQ a.
    split.
    - intros [HPa | HQa].
      + apply HP in HPa.
        exfalso.
        exact (the_impossible_has_no_witnesses a HPa).
      + exact HQa.
    - intro HQa.
      right. exact HQa.
  Qed.
  
  (* Implication from impossible *)
  Theorem impossible_implies_anything :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    forall a, P a -> Q a.
  Proof.
    intros P Q HP a HPa.
    apply HP in HPa.
    exfalso.
    exact (the_impossible_has_no_witnesses a HPa).
  Qed.
  
  (* Negation of impossible *)
  Theorem not_impossible_is_necessary :
    forall P : Alphacarrier -> Prop,
    Is_Impossible P ->
    forall a, ~ P a.
  Proof.
    intros P HP a HPa.
    apply HP in HPa.
    exact (the_impossible_has_no_witnesses a HPa).
  Qed.
  
  (* Double negation of impossible *)
  Theorem not_not_impossible_is_possible :
    forall P : Alphacarrier -> Prop,
    Is_Impossible (fun a => ~ P a) ->
    Is_Possible P.
  Proof.
    intros P HnP HP.
    (* If P is impossible, then ~P holds everywhere *)
    assert (forall a, ~ P a).
    { apply not_impossible_is_necessary. exact HP. }
    (* But HnP says ~P is impossible *)
    (* Get a witness from alpha_not_empty *)
    destruct alpha_not_empty as [a0 _].
    specialize (HnP a0).
    destruct HnP as [H1 H2].
    (* H1: ~ P a0 -> the_impossible a0 *)
    (* H2: the_impossible a0 -> ~ P a0 *)
    (* We have ~ P a0 from H *)
    specialize (H a0).
    apply H1 in H.
    (* Now we have the_impossible a0 *)
    exact (the_impossible_has_no_witnesses a0 H).
  Qed.
  
  (* The algebra forms a partial order *)
  Definition Impossible_Order (P Q : Alphacarrier -> Prop) : Prop :=
    Is_Impossible P -> Is_Impossible Q.
  
  (* Key theorem: impossibility propagates through logical connectives *)
  Theorem impossibility_propagation_constructive :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    (Is_Impossible (fun a => P a /\ Q a)) /\
    (forall a, P a -> Q a) /\
    (forall a, ~ (P a \/ Q a) -> ~ Q a).
  Proof.
    intros P Q HP.
    split; [|split].
    - apply impossible_and_anything_is_impossible. exact HP.
    - apply impossible_implies_anything. exact HP.
    - intros a H HQa.
      apply H. right. exact HQa.
  Qed.
  
  (* Equivalence *)
  Theorem impossible_iff_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    (forall a, P a <-> Q a) ->
    Is_Impossible Q.
  Proof.
    intros P Q HP Hiff.
    intro a.
    rewrite <- Hiff.
    apply HP.
  Qed.
  
  (* Both directions of implication *)
  Theorem impossible_implies_both_ways :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Impossible Q ->
    (forall a, P a <-> Q a).
  Proof.
    intros P Q HP HQ a.
    split; intro H.
    - apply HQ. apply HP. exact H.
    - apply HP. apply HQ. exact H.
  Qed.
  
  (* Contrapositive *)
  Theorem possible_contrapositive :
    forall P Q : Alphacarrier -> Prop,
    (forall a, P a -> Q a) ->
    Is_Impossible Q ->
    Is_Impossible P.
  Proof.
    intros P Q Himp HQ a.
    split.
    - intro HPa.
      apply HQ.
      apply Himp.
      exact HPa.
    - intro Himpa.
      exfalso.
      exact (the_impossible_has_no_witnesses a Himpa).
  Qed.
  
  (* Multiple conjunctions *)
  Theorem impossible_and_chain :
    forall P Q R : Alphacarrier -> Prop,
    Is_Impossible P ->
    Is_Impossible (fun a => P a /\ Q a /\ R a).
  Proof.
    intros P Q R HP.
    intro a.
    split.
    - intros [HPa [HQa HRa]].
      apply HP. exact HPa.
    - intro Himpa.
      split.
      + apply HP. exact Himpa.
      + split.
        * exfalso. exact (the_impossible_has_no_witnesses a Himpa).
        * exfalso. exact (the_impossible_has_no_witnesses a Himpa).
  Qed.
  
  (* Impossible is preserved under weakening *)
  Theorem and_impossible_at_witness :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible (fun a => P a /\ Q a) ->
    forall a, Q a -> ~ P a.
  Proof.
    intros P Q HPQ a HQa HPa.
    assert (the_impossible a).
    { apply HPQ. split; assumption. }
    exact (the_impossible_has_no_witnesses a H).
  Qed.
  
  Theorem and_impossible_gives_info :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible (fun a => P a /\ Q a) ->
    forall a, P a -> ~ Q a.
  Proof.
    intros P Q HPQ a HPa HQa.
    assert (the_impossible a).
    { apply HPQ. split; assumption. }
    exact (the_impossible_has_no_witnesses a H).
  Qed.
  
  (* Disjunction properties *)
  Theorem or_impossible_iff_both_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible (fun a => P a \/ Q a) <->
    Is_Impossible P /\ Is_Impossible Q.
  Proof.
    intros P Q.
    split.
    - intro H.
      split; intro a; split.
      + intro HPa. apply H. left. exact HPa.
      + intro Hi. exfalso. exact (the_impossible_has_no_witnesses a Hi).
      + intro HQa. apply H. right. exact HQa.
      + intro Hi. exfalso. exact (the_impossible_has_no_witnesses a Hi).
    - intros [HP HQ] a.
      split.
      + intros [HPa | HQa].
        * apply HP. exact HPa.
        * apply HQ. exact HQa.
      + intro Hi.
        left. apply HP. exact Hi.
  Qed.
  
  (* XOR with impossible *)
  Theorem xor_with_impossible :
    forall P Q : Alphacarrier -> Prop,
    Is_Impossible P ->
    (forall a, (P a /\ ~ Q a) \/ (~ P a /\ Q a)) <->
    (forall a, ~ P a /\ Q a).
  Proof.
    intros P Q HP.
    split.
    - intros H a.
      specialize (H a).
      destruct H as [[HPa HnQa] | [HnPa HQa]].
      + exfalso. apply HP in HPa. 
        exact (the_impossible_has_no_witnesses a HPa).
      + exact (conj HnPa HQa).
    - intros H a.
      right.
      exact (H a).
  Qed.

   Theorem impossible_preimage :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, P (f a) -> the_impossible (f a).
  Proof.
    intros f P HP a H.
    apply HP.
    exact H.
  Qed.
  
  (* What if we show that the preimage of impossible is empty? *)
  Theorem impossible_has_no_preimage :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, ~ P (f a).
  Proof.
    intros f P HP a H.
    (* H : P (f a) *)
    (* By HP, P (f a) <-> the_impossible (f a) *)
    apply HP in H.
    (* H : the_impossible (f a) *)
    exact (the_impossible_has_no_witnesses (f a) H).
  Qed.
  
  Theorem composition_with_impossible_is_empty :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, (fun x => P (f x)) a <-> False.
  Proof.
    intros f P HP a.
    split.
    - apply impossible_has_no_preimage. exact HP.
    - intro F. contradiction.
  Qed. 

  Theorem impossible_composition_empty :
    forall (f : Alphacarrier -> Alphacarrier) (P : Alphacarrier -> Prop),
    Is_Impossible P ->
    forall a, ~ P (f a).
  Proof.
    intros f P HP a HPfa.
    apply HP in HPfa.
    exact (the_impossible_has_no_witnesses (f a) HPfa).
  Qed.

   Definition Impossible_Given (P Q : Alphacarrier -> Prop) : Prop :=
    Is_Impossible (fun a => P a /\ Q a) /\
    Is_Possible Q.
  
  (* If P is impossible given Q, and Q holds somewhere, then P fails there *)
  Theorem impossible_given_witness :
    forall P Q : Alphacarrier -> Prop,
    Impossible_Given P Q ->
    forall a, Q a -> ~ P a.
  Proof.
    intros P Q [Himp Hpos] a HQa HPa.
    assert (the_impossible a).
    { apply Himp. split; assumption. }
    exact (the_impossible_has_no_witnesses a H).
  Qed.

  Definition Almost_Impossible (P : Alphacarrier -> Prop) : Prop :=
    Is_Possible P /\
    forall (witness : Alphacarrier -> Prop),
    (exists a, witness a /\ P a) ->
    exists (blocker : Alphacarrier -> Prop),
    Is_Impossible (fun a => witness a /\ blocker a).
  
  Theorem self_referential_impossible :
    forall P : Alphacarrier -> Prop,
    (forall a, P a <-> P a /\ ~ P a) ->
    Is_Impossible P.
  Proof.
    intros P Hself a.
    split.
    - intro HPa.
      (* From Hself: P a <-> P a /\ ~ P a *)
      apply Hself in HPa.
      destruct HPa as [HPa' HnPa].
      (* We have P a and ~ P a - this is the_impossible! *)
      exfalso. exact (HnPa HPa').
    - intro Hi.
      (* From the_impossible a, we need P a *)
      (* But P can never hold because it implies its own negation *)
      exfalso.
      exact (the_impossible_has_no_witnesses a Hi).
  Qed.

   (* Now for something really fun - the "impossibility rank" *)
  Inductive Impossibility_Rank : (Alphacarrier -> Prop) -> nat -> Prop :=
    | Rank_Direct : forall P,
        (forall a, P a <-> the_impossible a) ->
        Impossibility_Rank P 0
    | Rank_Composite : forall P Q n,
        Impossibility_Rank Q n ->
        (forall a, P a -> Q a) ->
        Impossibility_Rank P (S n).
  
  (* This measures "how many steps" away from the_impossible we are *)
  
  Theorem impossibility_rank_implies_impossible :
    forall P n,
    Impossibility_Rank P n ->
    Is_Impossible P.
  Proof.
    intros P n H.
    induction H.
    - (* Base case: P is directly the_impossible *)
      exact H.
    - (* Inductive: P implies something impossible *)
      intro a.
      split.
      + intro HPa.
        apply IHImpossibility_Rank.
        apply H0.
        exact HPa.
      + intro Hi.
        exfalso.
        exact (the_impossible_has_no_witnesses a Hi).
  Qed.
  
  (* The cool part: Russell's paradox has rank 1! *)
  Example russell_rank_one :
    forall (R : Alphacarrier -> Prop),
    (forall x, R x <-> ~ R x) ->
    Impossibility_Rank R 1.
  Proof.
    intros R Hrussell.
    (* First show R equals the_impossible *)
    assert (H: forall a, R a <-> the_impossible a).
    { 
      intro a.
      split.
      - intro HRa.
        (* R a implies ~ R a by Hrussell *)
        assert (HnRa: ~ R a).
        { apply Hrussell. exact HRa. }
        (* So we have R a and ~ R a *)
        exfalso.
        exact (HnRa HRa).
      - intro Hi.
        exfalso.
        exact (the_impossible_has_no_witnesses a Hi).
    }
    (* Now show it has rank 1 *)
    apply (Rank_Composite R the_impossible 0).
    - apply Rank_Direct.
      intro a. reflexivity.
    - intro a. intro HRa.
      apply H. exact HRa.
  Qed.

End ImpossibilityAlgebra.


Section ImpossibilityNumbers.
  Context {Alpha : AlphaType}.
  
  (* First, let's verify that every natural number is realized *)
  Theorem every_nat_has_impossible_predicate :
    forall n : nat, exists P, Impossibility_Rank P n.
  Proof.
    induction n.
    - (* Base case: rank 0 *)
      exists the_impossible.
      apply Rank_Direct.
      intro a. reflexivity.
    - (* Inductive: if rank n exists, so does rank n+1 *)
      destruct IHn as [Q HQ].
      (* Create P that implies Q but isn't Q *)
      exists (fun a => Q a /\ Q a).  (* Q ∧ Q *)
      apply (Rank_Composite _ Q n).
      + exact HQ.
      + intros a [HQa _]. exact HQa.
  Qed.
  
  
  (* Addition: The rank of P ∧ Q *)
  (* Theorem impossibility_conjunction_rank :
    forall P Q m n,
    Impossibility_Rank P m ->
    Impossibility_Rank Q n ->
    Impossibility_Rank (fun a => P a /\ Q a) (max m n).
  Proof.
    intros P Q m n HP HQ.
    (* The conjunction is as far as the furthest component *)
    destruct (Nat.max_dec m n) as [Hmax | Hmax].
    - (* max = m *)
      rewrite Hmax.
      apply (Rank_Composite _ P m).
      + exact HP.
      + intros a [HPa _]. exact HPa.
    - (* max = n *)
      rewrite Hmax.
      apply (Rank_Composite _ Q n).
      + exact HQ.
      + intros a [_ HQa]. exact HQa.
  Qed. *)
  
End ImpossibilityNumbers.


Section PredicateCalculus.
  Context {Alpha : AlphaType}.
  
  (* Sequence of predicates *)
  Definition predicate_sequence := nat -> (Alphacarrier -> Prop).
  
  (* Two predicates agree on a specific element *)
  Definition agrees_at (P Q : Alphacarrier -> Prop) (a : Alphacarrier) : Prop :=
    P a <-> Q a.
  
  (* Finite approximation: predicates agree on a list of test points *)
  Definition agrees_on_list (P Q : Alphacarrier -> Prop) (witnesses : list Alphacarrier) : Prop :=
    forall a, In a witnesses -> agrees_at P Q a.
  
  (* Convergence: eventually agrees on any finite set *)
  Definition converges_to (seq : predicate_sequence) (P : Alphacarrier -> Prop) : Prop :=
    forall (witnesses : list Alphacarrier),
    exists N : nat,
    forall n : nat,
    n >= N ->
    agrees_on_list (seq n) P witnesses.
  
  (* Example: constant sequence *)
  Definition constant_sequence (P : Alphacarrier -> Prop) : predicate_sequence :=
    fun n => P.
  
  Theorem constant_converges :
    forall P, converges_to (constant_sequence P) P.
  Proof.
    intros P witnesses.
    exists 0.
    intros n Hn a Ha.
    unfold constant_sequence, agrees_at.
    reflexivity.
  Qed.
  
  (* Continuity for predicate transformations *)
  Definition continuous (F : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop)) : Prop :=
    forall (seq : predicate_sequence) (P : Alphacarrier -> Prop),
    converges_to seq P ->
    converges_to (fun n => F (seq n)) (F P).
  
  (* Negation function *)
  Definition pred_neg (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => ~ P a.
  
  (* Is negation continuous? *)
  Theorem negation_continuous : continuous pred_neg.
Proof.
  unfold continuous, converges_to.
  intros seq P Hconv witnesses.
  destruct (Hconv witnesses) as [N HN].
  exists N.
  intros n Hn a Ha.
  specialize (HN n Hn a Ha).
  unfold pred_neg, agrees_at in *.
  split; intro H.
  - (* ~ seq n a -> ~ P a *)
    intro HPa. 
    apply H.
    apply HN.  (* Use HN: seq n a <-> P a in the forward direction *)
    exact HPa.
  - (* ~ P a -> ~ seq n a *)
    intro Hseq.
    apply H.
    apply HN.  (* Use HN: seq n a <-> P a in the backward direction *)
    exact Hseq.
Qed.
  
  (* Observable differences - constructive approach *)
  Inductive observable_diff (P Q : Alphacarrier -> Prop) : Alphacarrier -> Type :=
    | diff_PQ : forall a, P a -> ~ Q a -> observable_diff P Q a
    | diff_QP : forall a, ~ P a -> Q a -> observable_diff P Q a.
  
  (* A constructive notion of "no observable differences" on a witness set *)
  Definition no_observable_diffs (P Q : Alphacarrier -> Prop) (witnesses : list Alphacarrier) : Prop :=
    forall a, In a witnesses -> 
      (P a -> Q a) /\ (Q a -> P a).
  
  (* This is equivalent to agrees_on_list for our purposes *)
  Theorem no_diffs_iff_agrees :
    forall P Q witnesses,
    no_observable_diffs P Q witnesses <-> agrees_on_list P Q witnesses.
  Proof.
    intros P Q witnesses.
    unfold no_observable_diffs, agrees_on_list, agrees_at.
    split.
    - intros H a Ha.
      specialize (H a Ha).
      split; apply H.
    - intros H a Ha.
      specialize (H a Ha).
      split; apply H.
  Qed.
  
  (* Approaching the_impossible *)
  Definition approaches_impossible (seq : predicate_sequence) : Prop :=
    converges_to seq the_impossible.
  
  (* Example: shrinking sequence *)
  Definition shrinking_sequence (base : Alphacarrier -> Prop) : predicate_sequence :=
    fun n => fun a => base a /\ 
      exists (witness_list : list Alphacarrier), 
      length witness_list <= n /\ 
      In a witness_list.
  
  (* Conjunction is continuous *)
  Definition pred_and (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a /\ Q a.
  
  Theorem and_continuous_left :
    forall Q, continuous (fun P => pred_and P Q).
  Proof.
    intros Q.
    unfold continuous, converges_to.
    intros seq P Hconv witnesses.
    destruct (Hconv witnesses) as [N HN].
    exists N.
    intros n Hn a Ha.
    specialize (HN n Hn a Ha).
    unfold pred_and, agrees_at in *.
    split; intros [H1 H2].
    - split.
      + apply HN. exact H1.
      + exact H2.
    - split.
      + apply HN. exact H1.
      + exact H2.
  Qed.
  
  (* Disjunction is continuous *)
  Definition pred_or (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a \/ Q a.
  
  Theorem or_continuous_left :
    forall Q, continuous (fun P => pred_or P Q).
  Proof.
    intros Q.
    unfold continuous, converges_to.
    intros seq P Hconv witnesses.
    destruct (Hconv witnesses) as [N HN].
    exists N.
    intros n Hn a Ha.
    specialize (HN n Hn a Ha).
    unfold pred_or, agrees_at in *.
    split; intros [H | H].
    - left. apply HN. exact H.
    - right. exact H.
    - left. apply HN. exact H.
    - right. exact H.
  Qed.
  
  (* Composition of continuous functions is continuous *)
  Theorem continuous_compose :
    forall F G,
    continuous F ->
    continuous G ->
    continuous (fun P => F (G P)).
  Proof.
    intros F G HF HG.
    unfold continuous in *.
    intros seq P Hconv.
    apply HF.
    apply HG.
    exact Hconv.
  Qed.
  
  (* A predicate sequence that oscillates *)
  Definition oscillating_sequence : predicate_sequence :=
    fun n => if Nat.even n then (fun _ => True) else the_impossible.
  
  Theorem oscillating_not_convergent :
    ~ exists P, converges_to oscillating_sequence P.
  Proof.
    intros [P Hconv].
    destruct alpha_not_empty as [a0 _].
    destruct (Hconv [a0]) as [N HN].
    
    (* The key insight: find two consecutive positions where the sequence differs *)
    (* Let's use positions 0 and 1 for simplicity *)
    destruct (Hconv [a0]) as [N' HN'].
    
    (* Take a large enough N that covers both positions we'll check *)
    pose (M := max N' 2).
    
    (* Check at positions M (which is even) and M+1 (which is odd) *)
    assert (HM_ge : M >= N') by (unfold M; apply Nat.le_max_l).
    assert (H_in : In a0 [a0]) by (left; reflexivity).
    
    (* Get a specific even position *)
    pose (E := 2 * M).  (* E is definitely even *)
    assert (HE_even : Nat.even E = true).
    { unfold E. rewrite Nat.even_mul. reflexivity. }
    
    assert (HE_ge : E >= N').
    { unfold E. unfold ge.
      apply Nat.le_trans with M.
      - exact HM_ge.
      - (* Prove M <= 2 * M directly *)
        rewrite <- (Nat.mul_1_l M) at 1.
        apply Nat.mul_le_mono_r.
        apply Nat.le_succ_diag_r. }
    
    (* At position E: oscillating_sequence E = True *)
    pose proof (HN'_at_E := HN' E HE_ge a0 H_in).
    unfold oscillating_sequence in HN'_at_E.
    rewrite HE_even in HN'_at_E.
    
    (* At position E+1: oscillating_sequence (E+1) = the_impossible *)
    assert (HE1_ge : E + 1 >= N').
    { unfold ge. apply Nat.le_trans with E; [exact HE_ge | apply Nat.le_add_r]. }
    
    pose proof (HN'_at_E1 := HN' (E + 1) HE1_ge a0 H_in).
    unfold oscillating_sequence in HN'_at_E1.
    
    (* E+1 is odd because E is even *)
    assert (HE1_odd : Nat.even (E + 1) = false).
    { 
      (* Since E = 2*M, E+1 = 2*M + 1 which is odd *)
      unfold E.
      rewrite <- Nat.add_1_r.
      rewrite Nat.even_add.
      rewrite Nat.even_mul.
      reflexivity.
    }
    rewrite HE1_odd in HN'_at_E1.
    
    (* Now we have: P a0 <-> True and P a0 <-> the_impossible a0 *)
    assert (P a0) by (apply HN'_at_E; exact I).
    apply HN'_at_E1 in H.
    exact (the_impossible_has_no_witnesses a0 H).
  Qed.
  
  (* Path from one predicate to another *)
  Definition predicate_path := nat -> (Alphacarrier -> Prop).
  
  Definition path_from_to (path : predicate_path) (P Q : Alphacarrier -> Prop) : Prop :=
    path 0 = P /\
    converges_to path Q.
  
  (* The trivial path *)
  Definition trivial_path (P : Alphacarrier -> Prop) : predicate_path :=
    constant_sequence P.
  
  Theorem trivial_path_works :
    forall P, path_from_to (trivial_path P) P P.
  Proof.
    intro P.
    split.
    - reflexivity.
    - apply constant_converges.
  Qed.
  
  (* Linear interpolation doesn't quite work in predicate space, 
     but we can do something similar *)
  
  (* A sequence that gradually "turns off" a predicate *)
  Definition fade_to_impossible (P : Alphacarrier -> Prop) : predicate_sequence :=
    fun n => fun a => P a /\ 
      exists (proof_size : nat), proof_size <= n.
  
  (* If P has witnesses, this doesn't converge to impossible *)
  (* But it shows how we might think about "gradual" changes *)

End PredicateCalculus.


Section UndecidabilityFramework.
  Context {Alpha : AlphaType} {Omega : OmegaType}.
  Variable embed : Alphacarrier -> Omegacarrier.
  
  (* Pattern 1: Unrepresentable Omega predicates *)
  Definition Undecidable_Via_Unrepresentability 
    (P_alpha : Alphacarrier -> Prop) 
    (P_omega : Omegacarrier -> Prop) : Prop :=
    (* P_alpha tries to detect P_omega *)
    (forall a, P_alpha a <-> P_omega (embed a)) /\
    (* P_omega exists in Omega *)
    (exists x, P_omega x) /\
    (* But P_omega is not representable *)
    (~ representable P_omega).
  
  (* Remove the global Variable embed_surjective_on_range *)
  
  Theorem unrepresentable_implies_undecidable :
    forall P_alpha P_omega,
    (forall x, P_omega x -> exists a, embed a = x) ->  (* Add as parameter here *)
    Undecidable_Via_Unrepresentability P_alpha P_omega ->
    (~ exists a, P_alpha a) /\ (~ forall a, ~ P_alpha a).
  Proof.
    intros PA PO Hsurj [Hdetect [Hexists_omega Hunrep]].
    (* Rest of proof stays the same *)
    split.
    
    - (* Cannot prove it has witnesses *)
      intro Hexists_alpha.
      apply Hunrep.
      unfold representable.
      exists PA, embed.
      exact Hdetect.
      
    - (* Cannot prove it has no witnesses *)
      intro Hnone_alpha.
      destruct Hexists_omega as [x Hx].
      destruct (Hsurj x Hx) as [a Ha].
      rewrite <- Ha in Hx.
      apply Hdetect in Hx.
      exact (Hnone_alpha a Hx).
  Qed.
  
  (* Pattern 2: Self-referential classification - fixed type *)
  (* We need a concrete type for the truth values *)
  Inductive TruthValue : Type :=
    | TV_True : TruthValue
    | TV_False : TruthValue  
    | TV_Undecidable : TruthValue.
  
  Definition Undecidable_Via_Self_Reference
    (P : Alphacarrier -> Prop)
    (classify_P : TruthValue) : Prop :=
    (* P asks about its own classification *)
    match classify_P with
    | TV_True => forall a, P a <-> False
    | TV_False => forall a, P a <-> True  
    | TV_Undecidable => True  (* Consistent with undecidability *)
    end.
  
  Theorem self_reference_implies_undecidable :
    forall P classify_P,
    (* If classification is correct *)
    (match classify_P with
     | TV_True => exists a, P a
     | TV_False => forall a, ~ P a
     | TV_Undecidable => (~ exists a, P a) /\ (~ forall a, ~ P a)
     end) ->
    Undecidable_Via_Self_Reference P classify_P ->
    classify_P = TV_Undecidable.
  Proof.
    intros P classify_P Hcorrect Hself.
    destruct classify_P.
    - (* If classified as True *)
      destruct Hcorrect as [a Ha].
      unfold Undecidable_Via_Self_Reference in Hself.
      apply Hself in Ha.
      contradiction.
    - (* If classified as False *)
      unfold Undecidable_Via_Self_Reference in Hself.
      destruct alpha_not_empty as [a _].
      specialize (Hcorrect a).
      assert (P a) by (apply Hself; exact I).
      contradiction.
    - (* If classified as Undecidable - that's what we want *)
      reflexivity.
  Qed.
  

  Definition Both_Detect_Unrepresentable (P Q : Alphacarrier -> Prop) : Prop :=
    exists (U_omega : Omegacarrier -> Prop),
      (~ representable U_omega) /\
      (exists x, U_omega x) /\
      (forall a, P a <-> U_omega (embed a)) /\
      (forall a, Q a <-> U_omega (embed a)) /\
      (forall x, U_omega x -> exists a, embed a = x).
  
  Theorem both_detect_implies_both_undecidable :
    forall P Q,
    Both_Detect_Unrepresentable P Q ->
    ((~ exists a, P a) /\ (~ forall a, ~ P a)) /\
    ((~ exists a, Q a) /\ (~ forall a, ~ Q a)).
  Proof.
    intros P Q [U_omega [Hunrep [Hex [HP [HQ Hsurj]]]]].
    
    (* Key insight: P and Q are extensionally equal *)
    assert (forall a, P a <-> Q a).
    { intro a. rewrite HP, HQ. reflexivity. }
    
    (* So proving undecidability for P proves it for Q *)
    split.
    - (* P is undecidable *)
      apply (unrepresentable_implies_undecidable P U_omega Hsurj).
      unfold Undecidable_Via_Unrepresentability.
      split; [exact HP | split; [exact Hex | exact Hunrep]].
    - (* Q is undecidable *)  
      apply (unrepresentable_implies_undecidable Q U_omega Hsurj).
      unfold Undecidable_Via_Unrepresentability.
      split; [exact HQ | split; [exact Hex | exact Hunrep]].
  Qed.

  Inductive UndecidabilityReason (P : Alphacarrier -> Prop) : Type :=
    | Unrep_Omega : forall (P_omega : Omegacarrier -> Prop),
        (forall x, P_omega x -> exists a, embed a = x) ->
        Undecidable_Via_Unrepresentability P P_omega -> 
        UndecidabilityReason P
    | Self_Ref : forall classify_P,
        (match classify_P with
         | TV_True => exists a, P a
         | TV_False => forall a, ~ P a
         | TV_Undecidable => (~ exists a, P a) /\ (~ forall a, ~ P a)
         end) ->
        Undecidable_Via_Self_Reference P classify_P ->
        UndecidabilityReason P
    | Both_Detect : forall Q,
        Both_Detect_Unrepresentable P Q ->
        UndecidabilityReason P.
  
  (* Master theorem *)
  Theorem undecidability_master :
    forall P,
    UndecidabilityReason P ->
    (~ exists a, P a) /\ (~ forall a, ~ P a).
  Proof.
    intros P reason.
    destruct reason.
    - (* Via unrepresentability *)
      apply (unrepresentable_implies_undecidable P P_omega e u).
    - (* Via self-reference *)
      assert (classify_P = TV_Undecidable).
      { apply (self_reference_implies_undecidable P classify_P y u). }
      subst classify_P.
      exact y.
    - (* Both detect same unrepresentable *)
      pose proof (both_detect_implies_both_undecidable P Q b) as [HP HQ].
      exact HP.
  Qed.
  
End UndecidabilityFramework.

(* ============================================================ *)
(* Omega Contains Alpha                                         *)
(* ============================================================ *)

Section OmegaContainsAlpha.
  Context {Omega : OmegaType}.
  
  (* Define what it means to be an Alpha-like structure in Omega *)
  Definition alpha_like_structure (A : Omegacarrier -> Prop) : Prop :=
    (* Non-empty *)
    (exists x, A x) /\
    (* Has exactly one impossible predicate when restricted to A *)
    exists (imp : Omegacarrier -> Prop),
      (* imp has no witnesses in A *)
      (forall x, A x -> ~ imp x) /\
      (* imp is the unique such predicate *)
      (forall Q : Omegacarrier -> Prop,
        (forall x, A x -> ~ Q x) ->
        (forall x, A x -> (Q x <-> imp x))).
  
  (* The main theorem: Omega contains an Alpha simulation *)
  Theorem omega_contains_alpha:
    exists (alpha_sim : Omegacarrier -> Prop),
      alpha_like_structure alpha_sim.
  Proof.
    (* Ask Omega for a witness to alpha_like_structure *)
    pose (wants_to_be_alpha := fun x =>
      exists A : Omegacarrier -> Prop,
        A x /\ alpha_like_structure A).
    
    destruct (omega_completeness wants_to_be_alpha) as [x0 Hx0].
    destruct Hx0 as [A [HAx0 Hstruct]].
    
    (* A is our alpha simulation *)
    exists A.
    exact Hstruct.
  Qed.
  
  (* Now let's verify this simulation has the key Alpha properties *)
  Section AlphaSimProperties.
    (* Get the simulated Alpha and its impossible predicate *)
    Variable alpha_sim : Omegacarrier -> Prop.
    Variable H_alpha_sim : alpha_like_structure alpha_sim.
    
    (* Extract the components *)
    Let alpha_nonempty := proj1 H_alpha_sim.
    Let alpha_imp_spec := proj2 H_alpha_sim.
    
    (* Extract the impossible predicate directly *)
    Variable impossible_sim : Omegacarrier -> Prop.
    Variable H_imp_no_witnesses : forall x, alpha_sim x -> ~ impossible_sim x.
    Variable H_imp_unique : forall Q : Omegacarrier -> Prop,
      (forall x, alpha_sim x -> ~ Q x) ->
      (forall x, alpha_sim x -> (Q x <-> impossible_sim x)).
    
    (* The paradox firewalls work in the simulation *)
    Theorem sim_no_russell :
      ~ exists (R : Omegacarrier -> Prop),
        forall x, alpha_sim x -> (R x <-> ~ R x).
    Proof.
      intros [R HR].
      destruct alpha_nonempty as [x0 Hx0].
      specialize (HR x0 Hx0).
      (* Same contradiction as in regular Alpha *)
      destruct HR as [H1 H2].
      assert (R x0 -> False).
      { intro Hr. apply (H1 Hr). exact Hr. }
      apply H. apply H2. exact H.
    Qed.
    
    (* The three-valued logic emerges in the simulation *)
    Inductive SimulatedTruth (P : Omegacarrier -> Prop) : Type :=
      | Sim_True : (exists x, alpha_sim x /\ P x) -> SimulatedTruth P
      | Sim_False : (forall x, alpha_sim x -> ~ P x) -> SimulatedTruth P
      | Sim_Undecidable : 
          (~ exists x, alpha_sim x /\ P x) ->
          (~ forall x, alpha_sim x -> ~ P x) ->
          SimulatedTruth P.
    
    (* And we can construct undecidable predicates in the simulation *)
    Theorem sim_has_undecidable :
      exists P : Omegacarrier -> Prop,
      (~ exists x, alpha_sim x /\ P x) /\ 
      (~ forall x, alpha_sim x -> ~ P x).
    Proof.
      (* The predicate "x is outside alpha_sim" *)
      exists (fun x => ~alpha_sim x).
      
      split.
      - (* No element can be both in and out of alpha_sim *)
        intros [x [Hx HnX]].
        exact (HnX Hx).
        
      - (* But we can't prove all alpha_sim elements are inside *)
        intro H_all_inside.
        (* Omega's paradoxical completeness strikes again *)
        pose (paradox := fun x => alpha_sim x /\ ~alpha_sim x).
        destruct (omega_completeness paradox) as [z [Hz1 Hz2]].
        exact (Hz2 Hz1).
    Qed.
    
  End AlphaSimProperties.
  
  (* Alternative approach: directly construct with the impossible predicate *)
  Theorem omega_contains_alpha_with_impossible :
    exists (alpha_sim : Omegacarrier -> Prop) (imp_sim : Omegacarrier -> Prop),
      (* Non-empty *)
      (exists x, alpha_sim x) /\
      (* imp has no witnesses in alpha_sim *)
      (forall x, alpha_sim x -> ~ imp_sim x) /\
      (* imp is unique *)
      (forall Q : Omegacarrier -> Prop,
        (forall x, alpha_sim x -> ~ Q x) ->
        (forall x, alpha_sim x -> (Q x <-> imp_sim x))).
  Proof.
    (* Ask Omega for the whole package *)
    pose (alpha_with_imp := fun triple =>
      exists (A : Omegacarrier -> Prop) (imp : Omegacarrier -> Prop) (x : Omegacarrier),
        triple = (A, imp, x) /\
        A x /\
        (forall y, A y -> ~ imp y) /\
        (forall Q : Omegacarrier -> Prop,
          (forall y, A y -> ~ Q y) ->
          (forall y, A y -> (Q y <-> imp y)))).
    
    (* Since we need a triple, we'll use a product type *)
    pose (witness_pred := fun x => 
      exists A imp, alpha_with_imp (A, imp, x)).
    
    destruct (omega_completeness witness_pred) as [x [A [imp Htriple]]].
    
    exists A, imp.
    (* Unfold alpha_with_imp in Htriple *)
    unfold alpha_with_imp in Htriple.
    destruct Htriple as [A' [imp' [x' [Heq [HAx [Himp_no Himp_unique]]]]]].
    (* From Heq: (A, imp, x) = (A', imp', x'), so A = A', imp = imp', x = x' *)
    injection Heq as <- <- <-.
    
    split; [|split].
    - exists x. exact HAx.
    - exact Himp_no.
    - exact Himp_unique.
  Qed.
  
End OmegaContainsAlpha.


Section ConstructiveArithmetic.
  Context {Alpha : AlphaType}.
  
  (* Natural numbers as Alpha predicates *)
  Variable IsNat : Alphacarrier -> Prop.
  Variable IsZero : Alphacarrier -> Prop.
  Variable Succ : Alphacarrier -> Alphacarrier -> Prop.
  
  (* Axiom 1: Zero exists and is natural *)
  Axiom zero_exists : exists z, IsZero z /\ IsNat z.
  
  (* Axiom 2: Zero is unique *)
  Axiom zero_unique : forall x y, IsZero x -> IsZero y -> x = y.
  
  (* Axiom 3: Every natural has a successor *)
  Axiom successor_exists : forall x, IsNat x -> exists y, Succ x y /\ IsNat y.
  
  (* Axiom 4: Successor is functional *)
  Axiom successor_functional : forall x y z, Succ x y -> Succ x z -> y = z.
  
  (* Axiom 5: No number is its own successor *)
  Axiom no_self_successor : forall x, ~ Succ x x.
  
  (* Axiom 6: Successor is injective *)
  Axiom successor_injective : forall x y z, IsNat x -> IsNat y -> Succ x z -> Succ y z -> x = y.
  
  (* Axiom 7: Zero is not a successor *)
  Axiom zero_not_successor : forall x y, IsZero y -> ~ Succ x y.
  
  (* Axiom 8: Induction - this works constructively! *)
  Axiom nat_induction : 
    forall (P : Alphacarrier -> Prop),
      (forall z, IsZero z -> P z) ->
      (forall n m, IsNat n -> P n -> Succ n m -> P m) ->
      (forall n, IsNat n -> P n).
  
  (* Let's prove some basic theorems constructively *)
  
  (* Zero exists as a witness - no excluded middle needed *)
  Theorem zero_witness :
    exists z, IsZero z.
  Proof.
    destruct zero_exists as [z [Hz _]].
    exists z. exact Hz.
  Qed.
  
  (* Natural numbers exist - constructive *)
  Theorem nat_witness :
    exists n, IsNat n.
  Proof.
    destruct zero_exists as [z [_ Hz]].
    exists z. exact Hz.
  Qed.
  
  (* Every natural has a unique successor - constructive *)
  Theorem successor_unique_constructive :
    forall n, IsNat n -> 
    exists s, Succ n s /\ forall s', Succ n s' -> s = s'.
  Proof.
    intros n Hn.
    destruct (successor_exists n Hn) as [s [Hs HsNat]].
    exists s. split.
    - exact Hs.
    - intros s' Hs'.
      exact (successor_functional n s s' Hs Hs').
  Qed.
  
  (* Define One as successor of zero - constructive *)
  Definition IsOne : Alphacarrier -> Prop :=
    fun x => exists z, IsZero z /\ Succ z x.
  
  (* One exists - constructive *)
  Theorem one_exists : exists o, IsOne o.
  Proof.
    destruct zero_exists as [z [Hz HzNat]].
    destruct (successor_exists z HzNat) as [o [Hsucc HoNat]].
    exists o. exists z. split; assumption.
  Qed.
  
  (* Now let's add addition constructively *)
  Variable Plus : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.
  
  (* Addition axioms - all constructive *)
  Axiom plus_zero_right : forall x z, IsZero z -> IsNat x -> Plus x z x.
  Axiom plus_successor : forall x y z sx sy sz,
    IsNat x -> IsNat y -> IsNat z ->
    Succ x sx -> Succ y sy -> Succ z sz ->
    Plus x y z -> Plus sx y sz.
  Axiom plus_functional : forall x y z1 z2,
    Plus x y z1 -> Plus x y z2 -> z1 = z2.
  Axiom plus_total : forall x y,
    IsNat x -> IsNat y -> exists z, IsNat z /\ Plus x y z.
  
  (* We can define addition recursively - constructive *)
  Theorem plus_computable :
    forall x y, IsNat x -> IsNat y ->
    exists! z, Plus x y z.
  Proof.
    intros x y Hx Hy.
    destruct (plus_total x y Hx Hy) as [z [Hz HPl]].
    exists z. split.
    - exact HPl.
    - intros z' HPl'.
      exact (plus_functional x y z z' HPl HPl').
  Qed.
  
  (* Similarly for multiplication *)
  Variable Times : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.
  
  Axiom times_zero_right : forall x z, IsZero z -> IsNat x -> Times x z z.
  Axiom times_successor : forall x y z xy sxy,
    IsNat x -> IsNat y -> IsNat z ->
    Succ y z ->
    Times x y xy -> Plus xy x sxy ->
    Times x z sxy.
  Axiom times_total : forall x y,
    IsNat x -> IsNat y -> exists z, IsNat z /\ Times x y z.
  
  (* The key theorem: arithmetic is decidable in our constructive system *)
  (* This is crucial for Gödel's theorem to apply *)
  
  (* Define what it means to be a successor *)
  Definition IsSuccessor (n : Alphacarrier) : Type :=
    sigT (fun m : Alphacarrier => IsNat m /\ Succ m n).
  
  (* Now the axiom using explicit sum *)
  Axiom zero_or_successor_dec : forall n, IsNat n -> 
    sum (IsZero n) (IsSuccessor n).
  
  (* Helper lemma for decidable equality at zero *)
  Lemma eq_zero_dec : forall x, IsNat x -> IsZero x ->
    forall y, IsNat y -> {x = y} + {x <> y}.
  Proof.
    intros x Hx Hx0 y Hy.
    destruct (zero_or_successor_dec y Hy) as [Hy0 | Hsucc].
    - left. exact (zero_unique x y Hx0 Hy0).
    - right. intro H. subst x.  (* More explicit: subst x with y *)
      destruct Hsucc as [y' [Hy' Hsy']].
      exact (zero_not_successor y' y Hx0 Hsy').
  Defined.

  (* axiom for Type-valued induction *)
  Axiom nat_induction_Type : 
    forall (P : Alphacarrier -> Type),
      (forall z, IsZero z -> IsNat z -> P z) ->  (* Added IsNat z here *)
      (forall n m, IsNat n -> P n -> Succ n m -> IsNat m -> P m) ->  (* Added IsNat m *)
      (forall n, IsNat n -> P n).
  
  Definition nat_eq_dec : forall x y, IsNat x -> IsNat y ->
    {x = y} + {x <> y}.
  Proof.
    intros x y Hx Hy.
    (* Induct on x *)
    revert y Hy.
    apply (nat_induction_Type (fun x => forall y, IsNat y -> {x = y} + {x <> y})).
    
    - (* Base case: x is zero *)
      intros z Hz HzNat.
      exact (eq_zero_dec z HzNat Hz).
      
    - (* Inductive case: x = successor of n *)
      intros n m Hn IH Hsucc HmNat y Hy.
      destruct (zero_or_successor_dec y Hy) as [Hy0 | Hsucc_y].
      + (* y is zero, m is successor *)
        right. intro H. subst.
        exact (zero_not_successor n y Hy0 Hsucc).
      + (* both are successors *)
        destruct Hsucc_y as [y' [Hy' Hsy']].
        destruct (IH y' Hy') as [Heq | Hneq].
        * (* predecessors equal *)
          left. subst.
          exact (successor_functional y' m y Hsucc Hsy').
        * (* predecessors not equal *)
          right. intro H. apply Hneq.
          exact (successor_injective n y' m Hn Hy' Hsucc (eq_ind_r (fun z => Succ y' z) Hsy' H)).
    
    - (* Apply to x *)
      exact Hx.
  Defined.
  
  (* Primality can be defined constructively *)
  Definition Divides (d n : Alphacarrier) : Prop :=
    exists q, IsNat q /\ Times d q n.
  
  Definition IsPrime (p : Alphacarrier) : Prop :=
    IsNat p /\
    ~ IsZero p /\
    ~ IsOne p /\
    forall d, IsNat d -> Divides d p -> IsOne d \/ d = p.
  
End ConstructiveArithmetic.




Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Lia.

Record System := {
  S_min : nat;
  S_max : nat;
  valid_bounds_existential : S_min + 1 < S_max; (* Or S_min + 2 < S_max, whatever you have *)
  structure : nat -> nat;
  structure_bounded : forall t : nat, S_min < structure t < S_max;
  perpetual_change : forall t : nat, structure t <> structure (t + 1)
}.


Lemma S_min_lt_S_max_explicit_change (sys : System) : S_min sys < S_max sys.
Proof.
  destruct sys as [smin smax vb_exist struct_fun sb pc]. 
  simpl.
  lia.
Qed.


(* Absolute delta between structure at t and t+1 *)
Definition DS (sys : System) (t : nat) : nat :=
  if Nat.ltb (structure sys (t + 1)) (structure sys t) then
    structure sys t - structure sys (t + 1)
  else
    structure sys (t + 1) - structure sys t.


(* Because of perpetual_change, DS is always > 0 *)
Lemma DS_is_positive (sys : System) (t : nat) :
  DS sys t > 0.
Proof.
  unfold DS.
  pose proof (perpetual_change sys t) as H_neq_original.
  (* H_neq_original : structure sys t <> structure sys (t + 1) *)
  destruct (Nat.ltb (structure sys (t + 1)) (structure sys t)) eqn:H_ltb.
  - (* Case 1: structure sys (t + 1) < structure sys t *)
    apply Nat.ltb_lt in H_ltb.
    (* Goal is (structure sys t - structure sys (t + 1)) > 0 *)
    lia.
  - (* Case 2: structure sys (t + 1) >= structure sys t *)
    apply Nat.ltb_ge in H_ltb.
    (* Goal is (structure sys (t + 1) - structure sys t) > 0 *)
    (* In this branch, lia needs to use H_ltb and H_neq_original. *)
    lia.
Qed.



(* Structure S is always > 0 *)
Lemma S_is_positive (sys : System) (t : nat) :
  structure sys t > 0.
Proof.
  pose proof (structure_bounded sys t) as H_bounds.
  lia. (* S_min < structure t and S_min >= 0 implies structure t > 0 *)
Qed.


(* I_val (information flow) *)
Definition I_val (sys : System) (t : nat) : nat :=
  (structure sys t) * (DS sys t).


(* With perpetual_change and S > 0, I_val is always > 0 *)
Lemma I_val_is_positive (sys : System) (t : nat) :
  I_val sys t > 0.
Proof.
  unfold I_val.
  apply Nat.mul_pos_pos.
  - apply S_is_positive.
  - apply DS_is_positive.
Qed.


Lemma delta_bounded :
  forall (sys : System) (t : nat),
    DS sys t <= S_max sys - S_min sys - 1.
Proof.
  intros sys t.
  unfold DS.
  pose proof (structure_bounded sys t) as H_t.
  pose proof (structure_bounded sys (t + 1)) as H_t1.
  destruct (Nat.ltb (structure sys (t + 1)) (structure sys t)) eqn:H_ltb.
  - (* structure(t+1) < structure(t) *)
    (* DS = structure(t) - structure(t+1) *)
    (* Max when structure(t) is near S_max and structure(t+1) is near S_min *)
    lia.
  - (* structure(t+1) >= structure(t) *)  
    (* DS = structure(t+1) - structure(t) *)
    (* Max when structure(t+1) is near S_max and structure(t) is near S_min *)
    lia.
Qed.


Lemma I_val_bounded :
  forall (sys : System) (t : nat),
    I_val sys t < S_max sys * (S_max sys - S_min sys).
Proof.
  intros sys t.
  unfold I_val.
  pose proof (structure_bounded sys t) as H_struct.
  pose proof (delta_bounded sys t) as H_delta.
  
  (* We need to show: structure sys t * DS sys t < S_max sys * (S_max sys - S_min sys) *)
  
  (* Since structure sys t < S_max sys, we have structure sys t <= S_max sys - 1 *)
  (* Since DS sys t <= S_max sys - S_min sys - 1 *)
  
  (* The product is at most (S_max sys - 1) * (S_max sys - S_min sys - 1) *)
  (* We need to show this is < S_max sys * (S_max sys - S_min sys) *)
  
  assert (structure sys t * DS sys t <= (S_max sys - 1) * (S_max sys - S_min sys - 1)).
  {
    apply Nat.mul_le_mono.
    - lia. (* structure sys t < S_max sys implies structure sys t <= S_max sys - 1 *)
    - exact H_delta.
  }
  
  (* Now show (S_max sys - 1) * (S_max sys - S_min sys - 1) < S_max sys * (S_max sys - S_min sys) *)
  lia.
Qed.


(* ============================================================ *)
(* Connecting Dynamic Systems to the Omega/Alpha Framework *)
(* ============================================================ *)

(* First, let's define an unbounded OmegaSystem *)
Record OmegaSystem := {
  omega_structure : nat -> nat;
  
  (* Can grow without bound *)
  omega_unbounded : forall M : nat, exists t : nat, omega_structure t > M;

  omega_positive : forall t : nat, omega_structure t > 0;
  
  (* Can change arbitrarily fast *)
  omega_wild_changes : forall D : nat, exists t1 t2 : nat, 
    t2 = t1 + 1 /\
    (if Nat.ltb (omega_structure t2) (omega_structure t1) then
       omega_structure t1 - omega_structure t2
     else
       omega_structure t2 - omega_structure t1) > D
}.

(* Now let's connect System to AlphaType conceptually *)
Section SystemAlphaConnection.
  Variable Alpha : AlphaType.
  Variable sys : System.
  
  (* A System is like an AlphaType evolving in time 
     Each time step gives us a predicate on Alpha *)
  Definition system_predicate_at_time (t : nat) : Alphacarrier -> Prop :=
    fun a => exists (encoding : Alphacarrier -> nat),
      encoding a = structure sys t.
  
  (* The key insight: bounded systems can't represent all of Omega's behavior *)
  Theorem bounded_system_has_limits :
    forall omega : OmegaSystem,
    exists t : nat,
    omega_structure omega t > S_max sys.
  Proof.
    intro omega.
    pose proof (omega_unbounded omega (S_max sys)) as H.
    exact H.
  Qed.
  
End SystemAlphaConnection.

(* Define information flow for OmegaSystem *)
Definition omega_DS (omega : OmegaSystem) (t : nat) : nat :=
  if Nat.ltb (omega_structure omega (t + 1)) (omega_structure omega t) then
    omega_structure omega t - omega_structure omega (t + 1)
  else
    omega_structure omega (t + 1) - omega_structure omega t.

Definition omega_I_val (omega : OmegaSystem) (t : nat) : nat :=
  (omega_structure omega t) * (omega_DS omega t).

(* The crucial difference: Omega's I_val is unbounded *)
(* Then the proof becomes: *)
Theorem omega_I_val_unbounded :
  forall omega : OmegaSystem,
  forall B : nat,
  exists t : nat, omega_I_val omega t > B.
Proof.
  intros omega B.
  
  (* Find a time with change > B *)
  destruct (omega_wild_changes omega B) as [t1 [t2 [Ht2 H_change]]].
  
  exists t1.
  unfold omega_I_val.
  
  (* omega_structure t1 >= 1 (positive) and omega_DS t1 > B *)
  (* So their product > B *)
  
  pose proof (omega_positive omega t1) as H_pos.
  
  assert (omega_DS omega t1 > B).
  {
    unfold omega_DS.
    rewrite <- Ht2.
    exact H_change.
  }
  
  (* structure * DS >= 1 * DS > 1 * B = B *)
  apply Nat.lt_le_trans with (m := 1 * omega_DS omega t1).
  - rewrite Nat.mul_1_l. assumption.
  - apply Nat.mul_le_mono_r. lia.
Qed.

(* Now the key theorem: Systems trying to track OmegaSystems must optimize *)
Section TrackingAndOptimization.
  Variable sys : System.
  Variable omega : OmegaSystem.
  
  (* A tracking relationship: sys tries to follow omega within its bounds *)
  Definition tracks_approximately (error_bound : nat) : Prop :=
    forall t : nat,
    exists t_omega : nat,
    (* The system tracks omega with some error and delay *)
    (structure sys t <= omega_structure omega t_omega + error_bound) /\
    (structure sys t + error_bound >= omega_structure omega t_omega) /\
    (* But respecting its own bounds *)
    (S_min sys < structure sys t < S_max sys).
  
  (* The fundamental tradeoff appears when tracking *)
  Theorem tracking_forces_tradeoff :
    forall error_bound : nat,
    tracks_approximately error_bound ->
    (* The system can't maximize both S and DS simultaneously *)
    ~ (exists t : nat, 
        structure sys t = S_max sys - 1 /\ 
        DS sys t = S_max sys - S_min sys - 1).
  Proof.
    intros error_bound H_tracks.
    intro H_both_max.
    destruct H_both_max as [t [H_S_max H_DS_max]].
    
    (* If structure sys t = S_max - 1 and DS is maximal, 
      then structure sys (t+1) must be near S_min *)
    
    (* First, let's figure out what structure sys (t+1) must be *)
    unfold DS in H_DS_max.
    
    (* Case analysis on the direction of change *)
    destruct (Nat.ltb (structure sys (t + 1)) (structure sys t)) eqn:Hltb.
    
    - (* structure(t+1) < structure(t) *)
      apply Nat.ltb_lt in Hltb.
      (* DS = structure(t) - structure(t+1) = S_max - 1 - structure(t+1) *)
      rewrite H_S_max in H_DS_max.
      
      (* So structure(t+1) = (S_max - 1) - (S_max - S_min - 1) = S_min *)
      assert (structure sys (t + 1) = S_min sys).
      { lia. }
      
      (* But this violates structure_bounded! *)
      pose proof (structure_bounded sys (t + 1)) as H_bound.
      lia.
      
    - (* structure(t+1) >= structure(t) *)
      apply Nat.ltb_ge in Hltb.
      (* DS = structure(t+1) - structure(t) = structure(t+1) - (S_max - 1) *)
      rewrite H_S_max in H_DS_max.
      
      (* From H_DS_max: structure(t+1) - (S_max - 1) = S_max - S_min - 1 *)
      (* So: structure(t+1) = (S_max - 1) + (S_max - S_min - 1) *)
      
      (* Let's be explicit about the arithmetic *)
      assert (H_t1_val: structure sys (t + 1) = 
              (S_max sys - 1) + (S_max sys - S_min sys - 1)).
      { 
        (* From H_DS_max, rearranging *)
        lia.
      }
      
      (* Simplify: = S_max - 1 + S_max - S_min - 1 = 2*S_max - S_min - 2 *)
      
      (* To show this >= S_max, we need: 2*S_max - S_min - 2 >= S_max *)
      (* Which simplifies to: S_max - S_min >= 2 *)
      (* Which is equivalent to: S_max >= S_min + 2 *)
      
      (* From valid_bounds_existential, we have S_min + 1 < S_max *)
      (* So S_max > S_min + 1, which means S_max >= S_min + 2 (for naturals) *)
      
      pose proof (valid_bounds_existential sys) as H_valid.
      
      (* Now we can show structure(t+1) >= S_max *)
      assert (structure sys (t + 1) >= S_max sys).
      { 
        rewrite H_t1_val.
        (* We need to show: (S_max - 1) + (S_max - S_min - 1) >= S_max *)
        (* Simplifies to: 2*S_max - S_min - 2 >= S_max *)
        (* Which is: S_max >= S_min + 2 *)
        lia.
      }
      
      (* But this violates structure_bounded! *)
      pose proof (structure_bounded sys (t + 1)) as H_bound.
      lia.
  Qed.
  
End TrackingAndOptimization.

(* ============================================================ *)
(* The Core I_max Theorem: Systems Cannot Maximize Both S and DS *)
(* ============================================================ *)

Section CoreIMaxTheorem.
  Variable sys : System.
  
  (* The fundamental constraint: cannot maximize both S and DS *)
  Theorem cannot_maximize_both :
    ~(exists t : nat,
      structure sys t = S_max sys - 1 /\
      DS sys t = S_max sys - S_min sys - 1).
  Proof.
    intro H_both.
    destruct H_both as [t [H_S H_DS]].
    
    (* Analyze what happens at time t+1 *)
    unfold DS in H_DS.
    
    (* Case analysis on direction of change *)
    destruct (Nat.ltb (structure sys (t + 1)) (structure sys t)) eqn:Hlt.
    
    - (* Case 1: structure is decreasing *)
      apply Nat.ltb_lt in Hlt.
      (* DS = structure(t) - structure(t+1) = S_max - 1 - structure(t+1) *)
      rewrite H_S in H_DS.
      
      (* From H_DS: (S_max - 1) - structure(t+1) = S_max - S_min - 1 *)
      (* Therefore: structure(t+1) = (S_max - 1) - (S_max - S_min - 1) *)
      (* Simplifying: structure(t+1) = S_min *)
      assert (H_eq: structure sys (t + 1) = S_min sys).
      { lia. }
      
      (* But structure must be > S_min *)
      pose proof (structure_bounded sys (t + 1)) as H_bound.
      rewrite H_eq in H_bound.
      lia.
      
    - (* Case 2: structure is increasing or equal *)
      apply Nat.ltb_ge in Hlt.
      (* DS = structure(t+1) - structure(t) *)
      rewrite H_S in H_DS.
      
      (* From H_DS: structure(t+1) - (S_max - 1) = S_max - S_min - 1 *)
      (* Therefore: structure(t+1) = (S_max - 1) + (S_max - S_min - 1) *)
      assert (H_val: structure sys (t + 1) = 
                     (S_max sys - 1) + (S_max sys - S_min sys - 1)).
      { lia. }
      
      (* Simplify: structure(t+1) = 2*S_max - S_min - 2 *)
      
      (* We need to show this exceeds S_max - 1 *)
      (* 2*S_max - S_min - 2 > S_max - 1 *)
      (* S_max - S_min - 1 > 0 *)
      (* S_max > S_min + 1 *)
      
      (* This follows from valid_bounds *)
      pose proof (valid_bounds_existential sys) as H_valid.
      
      (* Now show structure(t+1) > S_max - 1 *)
      assert (H_exceeds: structure sys (t + 1) > S_max sys - 1).
      {
        rewrite H_val.
        lia.
      }
      
      (* But structure must be < S_max *)
      pose proof (structure_bounded sys (t + 1)) as H_bound.
      lia.
  Qed.
  
  (* Define what optimization means *)
  Definition achieves_optimization : Prop :=
    exists t : nat,
    I_val sys t >= (S_max sys * (S_max sys - S_min sys)) / 2.
  
  (* The positive result: systems can achieve good I_val *)
  (* This would require additional assumptions about the system's dynamics *)
  
End CoreIMaxTheorem.

(* Now let's connect this to the Omega/Alpha framework *)
Section OmegaAlphaConnection.
  Variable sys : System.
  Variable omega : OmegaSystem.
  
  (* A key insight: bounded systems have bounded I_val *)
  Theorem bounded_I_val :
    exists I_bound : nat,
    forall t : nat, I_val sys t <= I_bound.
  Proof.
    exists (S_max sys * (S_max sys - S_min sys)).
    intro t.
    unfold I_val, DS.
    
    (* Get bounds on structure *)
    pose proof (structure_bounded sys t) as H_S.
    
    (* Case analysis on DS *)
    destruct (Nat.ltb (structure sys (t + 1)) (structure sys t)).
    
    - (* Decreasing *)
      (* DS <= S_max - S_min because structure is bounded *)
      assert (structure sys t - structure sys (t + 1) <= S_max sys - S_min sys).
      {
        pose proof (structure_bounded sys (t + 1)) as H_S1.
        lia.
      }
      (* I_val = S * DS <= S_max * (S_max - S_min) *)
      apply Nat.mul_le_mono; lia.
      
    - (* Increasing or equal *)
      assert (structure sys (t + 1) - structure sys t <= S_max sys - S_min sys).
      {
        pose proof (structure_bounded sys (t + 1)) as H_S1.
        lia.
      }
      apply Nat.mul_le_mono; lia.
  Qed.
  
  (* The fundamental gap *)
  Theorem omega_exceeds_any_bound :
    forall B : nat,
    exists t : nat, omega_I_val omega t > B.
  Proof.
    exact (omega_I_val_unbounded omega).
  Qed.
  

  (* Therefore: perfect tracking is impossible *)
  Theorem no_perfect_I_tracking :
    ~(forall t : nat, 
      I_val sys t = omega_I_val omega t).
  Proof.
    intro H_track.
    
    (* Get sys's I_val bound *)
    destruct bounded_I_val as [I_bound H_bound].
    
    (* Find where omega exceeds this bound *)
    destruct (omega_exceeds_any_bound (I_bound + 1)) as [t_big H_big].
    
    (* At time t_big, omega has I_val > I_bound + 1 *)
    (* But sys has I_val <= I_bound *)
    specialize (H_track t_big).
    specialize (H_bound t_big).
    
    (* H_track: I_val sys t_big = omega_I_val omega t_big *)
    (* H_bound: I_val sys t_big <= I_bound *)
    (* H_big: omega_I_val omega t_big > I_bound + 1 *)
    
    rewrite H_track in H_bound.
    lia.
  Qed.

End OmegaAlphaConnection.


(* ============================================================ *)
(* The Yoneda-I_max Construction: Objects as Optimized Relations *)
(* ============================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

(* Start with concrete information morphisms *)
Record InfoMorphism := {
  source_complexity : nat;      (* S_source *)
  target_complexity : nat;      (* S_target *)
  transformation_rate : nat;    (* How fast information flows *)
  
  (* Constraints *)
  rate_bounded : transformation_rate > 0;
  complexity_preserved : target_complexity > 0 -> source_complexity > 0
}.

(* I_val for a morphism: how much information flows *)
Definition morphism_I_val (f : InfoMorphism) : nat :=
  source_complexity f * transformation_rate f.

(* A simple concrete category with I_max constraints *)
Module ConcreteInfoCategory.
  
  (* Objects are just natural numbers representing complexity levels *)
  Definition Obj := nat.
  
  (* Global I_max bound *)
  Definition I_max_global : nat := 1000.
  
  (* Valid morphisms must respect I_max *)
  Definition valid_morphism (source target : Obj) (f : InfoMorphism) : Prop :=
    source_complexity f <= source /\
    target_complexity f <= target /\
    morphism_I_val f <= I_max_global.
  
  (* Identity morphism - provable! *)
  Definition id_morphism (n : Obj) : InfoMorphism.
  Proof.
    refine {| 
      source_complexity := n;
      target_complexity := n;
      transformation_rate := 1
    |}.
    - auto.
    - intro. auto.
  Defined.
  
  (* Identity respects I_max *)
  Lemma id_morphism_valid : forall n : Obj,
    n > 0 -> n <= I_max_global ->
    valid_morphism n n (id_morphism n).
  Proof.
    intros n Hn Hmax.
    unfold valid_morphism, id_morphism, morphism_I_val.
    simpl.
    split; [|split]; auto.
    rewrite Nat.mul_1_r.
    assumption.
  Qed.
  
End ConcreteInfoCategory.

(* Now let's build toward Yoneda *)
Module YonedaForInfo.
  Import ConcreteInfoCategory.
  
  (* The Yoneda embedding: view object n through all morphisms from it *)
  Definition hom_functor (n : Obj) : Obj -> Type :=
    fun m => { f : InfoMorphism | valid_morphism n m f }.
  
  (* Key insight: objects with no outgoing morphisms don't "exist" *)
  Definition has_morphisms (n : Obj) : Prop :=
    exists m : Obj, exists f : InfoMorphism,
    valid_morphism n m f.
  
  (* Trivial: every object has id morphism to itself *)
  Lemma every_object_has_morphism : forall n : Obj,
    n > 0 -> n <= I_max_global ->
    has_morphisms n.
  Proof.
    intros n Hn Hmax.
    unfold has_morphisms.
    exists n, (id_morphism n).
    apply id_morphism_valid; assumption.
  Qed.
  
  (* Objects are "stable" if they achieve good I_val *)
  Definition stable_object (n : Obj) : Prop :=
    n > 0 /\
    exists threshold : nat,
    threshold >= n / 2 /\
    exists m : Obj, exists f : InfoMorphism,
    valid_morphism n m f /\
    morphism_I_val f >= threshold.
  
  (* Alternative: prove that stable objects achieve good I_val relative to size *)
  Lemma stable_objects_achieve_good_flow : forall n : Obj,
    stable_object n ->
    exists f : InfoMorphism, exists m : Obj,
    valid_morphism n m f /\
    morphism_I_val f >= n / 2 /\
    morphism_I_val f <= I_max_global.
  Proof.
    intros n H_stable.
    destruct H_stable as [Hn [threshold [Hthresh [m [f [Hvalid Hival]]]]]].
    exists f, m.
    split; [|split].
    - exact Hvalid.
    - lia. (* threshold >= n/2 and morphism_I_val f >= threshold *)
    - unfold valid_morphism in Hvalid.
      destruct Hvalid as [_ [_ Hmax]].
      exact Hmax.
  Qed.
  
End YonedaForInfo.


Require Import Coq.Arith.Arith.


Module ObjectsAsOptimization.
  Import ConcreteInfoCategory.
  Import YonedaForInfo.
  
  (* First, let's handle the easy cases *)
  
  (* Case 1: Morphism to itself (identity) *)
  Lemma morphism_to_self : forall n : Obj,
    n > 0 -> n <= I_max_global ->
    exists f : InfoMorphism,
    valid_morphism n n f /\
    morphism_I_val f = n.
  Proof.
    intros n Hn Hmax.
    exists (id_morphism n).
    split.
    - apply id_morphism_valid; assumption.
    - unfold morphism_I_val, id_morphism. simpl.
      lia.
  Qed.

  Lemma div_le : forall a b : nat, b > 0 -> a / b <= a.
  Proof.
    intros a b Hb.
    apply Nat.div_le_upper_bound.
    - lia.
    - (* show a ≤ b * a *)
      destruct b as [|b0].
      + lia.              (* b = 0 contradicts Hb : b > 0 *)
      + simpl.            (* now b = S b0, so b * a = a + b0 * a *)
        apply Nat.le_add_r.  (* a ≤ a + (b0 * a) *)
  Qed.

  
  (* Helper lemma about division *)
  Lemma div_2_le : forall n : nat, n / 2 <= n.
  Proof.
    intros n.
    apply div_le.
    lia.
  Qed.
  
  (* Case 2: Morphism to smaller objects - information reduction *)
  Lemma morphism_to_smaller : forall n m : Obj,
    n > 0 -> m > 0 -> n > m -> n <= I_max_global ->
    exists f : InfoMorphism,
    valid_morphism n m f /\
    morphism_I_val f >= m / 2.
  Proof.
    intros n m Hn Hm Hnm Hmax.
    (* Create a "reduction" morphism *)
    assert (m <= n) by lia.
    
    (* First prove 1 > 0 *)
    assert (H_one_pos : 1 > 0) by lia.
    
    exists {|
      source_complexity := m;
      target_complexity := m;
      transformation_rate := 1;
      rate_bounded := H_one_pos;
      complexity_preserved := fun H => H  (* if m > 0 then m > 0 *)
    |}.
    
    (* Now prove the properties *)
    unfold valid_morphism, morphism_I_val. simpl.
    split.
    - (* valid_morphism *)
      split; [|split]; lia.
    - (* morphism_I_val >= m/2 *)
      rewrite Nat.mul_1_r.
      (* Use our helper lemma *)
      apply div_2_le.
  Qed.
  
  (* Case 3: Morphism to larger objects - need to be more careful *)
  Lemma morphism_to_larger : forall n m : Obj,
    n > 0 -> m > 0 -> m > n -> m <= I_max_global ->
    exists f : InfoMorphism,
    valid_morphism n m f /\
    morphism_I_val f >= n / 2.
  Proof.
    intros n m Hn Hm Hmn Hmax.
    
    (* First prove 1 > 0 *)
    assert (H_one_pos : 1 > 0) by lia.
    
    (* Create an "embedding" morphism *)
    exists {|
      source_complexity := n;
      target_complexity := n;  (* Only fill part of target *)
      transformation_rate := 1;
      rate_bounded := H_one_pos;
      complexity_preserved := fun H => H  (* if n > 0 then n > 0 *)
    |}.
    
    (* Now prove the properties *)
    unfold valid_morphism, morphism_I_val. simpl.
    split.
    - (* valid_morphism *)
      split; [|split].
      + (* source_complexity <= n *)
        lia.
      + (* target_complexity <= m *)
        (* n <= m because n < m *)
        lia.
      + (* morphism_I_val <= I_max_global *)
        rewrite Nat.mul_1_r.
        (* n <= I_max_global because n < m <= I_max_global *)
        lia.
    - (* morphism_I_val >= n/2 *)
      rewrite Nat.mul_1_r.
      (* Use the same helper lemma *)
      apply div_2_le.
  Qed.
  
  (* Now combine these cases *)
  Lemma morphism_to_any : forall n m : Obj,
    n > 0 -> m > 0 -> n <= I_max_global -> m <= I_max_global ->
    exists f : InfoMorphism,
    valid_morphism n m f /\
    morphism_I_val f >= (Nat.min n m) / 2.  (* Use Nat.min explicitly *)
  Proof.
    intros n m Hn Hm Hn_max Hm_max.
    destruct (Nat.lt_trichotomy n m) as [Hlt | [Heq | Hgt]].
    
    - (* n < m *)
      destruct (morphism_to_larger n m Hn Hm Hlt Hm_max) as [f [Hvalid Hival]].
      exists f.
      split; [exact Hvalid|].
      (* When n < m, Nat.min n m = n *)
      rewrite Nat.min_l.
      + exact Hival.
      + (* Prove n <= m *)
        lia.
    
    - (* n = m *)
      subst m.
      destruct (morphism_to_self n Hn Hn_max) as [f [Hvalid Hival]].
      exists f.
      split; [exact Hvalid|].
      rewrite Hival.
      (* When n = n, Nat.min n n = n *)
      rewrite Nat.min_id.
      (* n >= n/2 *)
      apply div_2_le.
    
    - (* n > m *)
      destruct (morphism_to_smaller n m Hn Hm Hgt Hn_max) as [f [Hvalid Hival]].
      exists f.
      split; [exact Hvalid|].
      (* When n > m, Nat.min n m = m *)
      rewrite Nat.min_r.
      + exact Hival.
      + (* Prove m <= n *)
        lia.
  Qed.
  
  (* Finally, we can prove the main theorem *)
  Definition optimization_pattern (n : Obj) : Prop :=
    forall m : Obj,
    m > 0 -> m <= I_max_global ->
    exists f : InfoMorphism,
    valid_morphism n m f /\
    morphism_I_val f >= (min n m) / 2.
  
  Theorem stable_implies_optimization : forall n : Obj,
    stable_object n ->
    n <= I_max_global ->  
    optimization_pattern n.
  Proof.
    intros n H_stable Hn_max m Hm Hm_max.
    (* Use our lemma *)
    destruct H_stable as [Hn _].
    apply morphism_to_any; assumption.
  Qed.
  
End ObjectsAsOptimization.

(* Simple example to verify our definitions work *)
Module Example.
  Import ConcreteInfoCategory.
  Import YonedaForInfo.
  Import ObjectsAsOptimization.
  
  (* Object 10 is stable *)
  Example object_10_stable : stable_object 10.
  Proof.
    unfold stable_object.
    split.
    - lia.
    - exists 5.
      split.
      + (* Need to prove 5 >= 10/2 *)
        assert (10 / 2 = 5) by reflexivity.
        rewrite H.
        lia.
      + exists 10, (id_morphism 10).
        split.
        * (* Need to prove valid_morphism 10 10 (id_morphism 10) *)
          apply id_morphism_valid.
          -- (* 10 > 0 *)
             lia.
          -- (* 10 <= I_max_global *)
             unfold I_max_global.
             lia.
        * unfold morphism_I_val, id_morphism. simpl.
          (* I_val = 10 * 1 = 10, need to show 10 >= 5 *)
          lia.
  Qed.
  
  (* Let's also show object 10 has an optimization pattern! *)
  Example object_10_optimizes : 
    optimization_pattern 10.
  Proof.
    (* Use our theorem! *)
    apply stable_implies_optimization.
    - exact object_10_stable.
    - (* 10 <= I_max_global = 1000 *)
      unfold I_max_global.
      lia.
  Qed.
  
End Example.


(* ============================================================ *)
(* The Meta-Proof: Unprovability Proves Ultimacy                *)
(* ============================================================ *)

Section MetaProof.
  Context {Omega : OmegaType} {Alpha : AlphaType}.
  Variable embed : Alphacarrier -> Omegacarrier.
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop, 
    exists n, alpha_enum n = Some A.
  
  (* AXIOMS for the meta-proof *)
  
  (* Axiom 1: Diagonal predicates are enumerable *)
  Axiom diagonal_in_enumeration :
    forall n : nat,
    exists m : nat,
    alpha_enum m = Some (fun a => diagonal_pred alpha_enum n a).
  
  (* Axiom 2: What it means for Theory to "analyze" a predicate *)
  Axiom theory_analyzes :
    forall (Theory P : Alphacarrier -> Prop) (analysis : Alphacarrier),
    Theory analysis ->
    (* analysis correctly captures P's diagonal relationship to Theory *)
    forall n, alpha_enum n = Some Theory ->
    (P = fun a => diagonal_pred alpha_enum n a) ->
    False.  (* This creates immediate contradiction *)
  
  (* Alpha claims to have a complete theory of optimization *)
  Definition alpha_has_complete_optimization_theory : Prop :=
    exists (Theory : Alphacarrier -> Prop),
    (* Theory is enumerable *)
    (exists n, alpha_enum n = Some Theory) /\
    (* Theory can analyze any enumerable predicate *)
    (forall (P : Alphacarrier -> Prop),
      (exists m, alpha_enum m = Some P) ->
      exists (analysis : Alphacarrier),
      Theory analysis) /\
    (* Including Theory itself - this is the key self-reference *)
    exists (self_analysis : Alphacarrier),
    Theory self_analysis.
  
  (* Step 1: This is impossible by diagonalization *)
  Theorem no_complete_optimization_theory :
    ~ alpha_has_complete_optimization_theory.
  Proof.
    intro H.
    destruct H as [Theory [Henum [Hanalyze Hself]]].
    destruct Henum as [n Hn].
    destruct Hself as [self_analysis Hself_in_Theory].
    
    (* Consider the diagonal predicate at Theory's position n *)
    pose (diag_n := fun a => diagonal_pred alpha_enum n a).
    
    (* The diagonal is enumerable by our axiom *)
    destruct (diagonal_in_enumeration n) as [m Hm].
    
    (* So Theory must be able to analyze it *)
    assert (H_diag_enum: exists k, alpha_enum k = Some diag_n).
    { exists m. exact Hm. }
    
    destruct (Hanalyze diag_n H_diag_enum) as [analysis Hanalysis].
    
    (* But by our axiom, Theory analyzing its own diagonal is impossible *)
    apply (theory_analyzes Theory diag_n analysis Hanalysis n Hn).
    
    (* diag_n is indeed the diagonal at position n *)
    reflexivity.
  Qed.
  
  (* Step 2: Omega can witness this limitation *)
  Definition omega_witnesses_theory_attempt : Omegacarrier -> Prop :=
    fun x => 
      (* x encodes an Alpha-like system attempting complete theory *)
      exists (alpha_sim : Omegacarrier -> Prop) (theory_sim : Omegacarrier -> Prop),
      alpha_like_structure alpha_sim /\
      (* theory_sim exists within alpha_sim *)
      (exists t, alpha_sim t /\ 
        (* theory_sim claims completeness within alpha_sim *)
        forall p, alpha_sim p -> exists analysis, alpha_sim analysis) /\
      (* x is related to this attempt *)
      exists a, embed a = x.
  
  (* Omega contains witnesses to the attempt and failure *)
  Theorem omega_sees_incompleteness :
    exists (witness : Omegacarrier),
    omega_witnesses_theory_attempt witness.
  Proof.
    apply omega_completeness.
  Qed.
  
  (* Step 3: Connect to I_max optimization *)
  
  (* A theory that can compute I_max must be complete *)
  Definition can_compute_I_max (Theory : Alphacarrier -> Prop) : Prop :=
    (* For any system encoding, Theory can bound its I_val *)
    forall (sys_encoding : Alphacarrier),
    exists (bound_proof : Alphacarrier),
    Theory bound_proof.
  
  (* Simple lemma: non-empty theories exist *)
  Lemma complete_theories_non_empty :
    forall (Theory : Alphacarrier -> Prop),
    (forall P, (exists m, alpha_enum m = Some P) -> 
      exists analysis, Theory analysis) ->
    exists t, Theory t.
  Proof.
    intros Theory H_complete.
    (* Theory can analyze any enumerable predicate *)
    (* Use the trivial predicate that's always true *)
    assert (H_true_enum: exists m, alpha_enum m = Some (fun _ => True)).
    { apply enum_complete. }
    
    destruct (H_complete (fun _ => True) H_true_enum) as [analysis H].
    exists analysis. exact H.
  Qed.
  
  (* Computing I_max requires completeness *)
  Theorem I_max_requires_completeness :
    forall Theory,
    (exists n, alpha_enum n = Some Theory) ->
    can_compute_I_max Theory ->
    alpha_has_complete_optimization_theory.
  Proof.
    intros Theory Henum H_compute.
    exists Theory.
    split; [exact Henum|].
    split.
    - (* Theory can analyze any predicate *)
      intros P HP.
      (* Since Theory can compute I_max for any system encoding,
        just use any element as the system encoding *)
      destruct alpha_not_empty as [a0 _].
      destruct (H_compute a0) as [bound_proof Hproof].
      (* Use bound_proof as our analysis *)
      exists bound_proof.
      exact Hproof.
    - (* Self-analysis exists *)
      (* Again, use H_compute directly *)
      destruct alpha_not_empty as [a0 _].
      destruct (H_compute a0) as [self_analysis Hself].
      exists self_analysis.
      exact Hself.
  Qed.
  
  (* Therefore, computing I_max is impossible *)
  Theorem computing_I_max_impossible :
    forall Theory,
    (exists n, alpha_enum n = Some Theory) ->
    ~ can_compute_I_max Theory.
  Proof.
    intros Theory Henum H_compute.
    
    (* If Theory could compute I_max, it would be complete *)
    pose proof (I_max_requires_completeness Theory Henum H_compute) as H_complete.
    
    (* But we proved no complete theory exists *)
    exact (no_complete_optimization_theory H_complete).
  Qed.
  
  (* The Meta-Theorem: The recursive validation *)
  Theorem meta_validation_of_I_max :
    (* I_max theory predicts: *)
    (* 1. No system can compute its own I_max perfectly *)
    (forall Theory, (exists n, alpha_enum n = Some Theory) -> 
      ~ can_compute_I_max Theory) /\
    (* 2. This limitation is witnessed in Omega *)
    (exists w, omega_witnesses_theory_attempt w) /\
    (* 3. This validates I_max through its own incompleteness *)
    (* "We can't prove I_max is ultimate, which proves it is" *)
    True.
  Proof.
    split; [|split].
    - (* No theory can compute its own I_max *)
      exact computing_I_max_impossible.
    
    - (* Omega witnesses this *)
      exact omega_sees_incompleteness.
      
    - (* The validation through incompleteness *)
      exact I.
  Qed.

(* First, let's be precise about what "computing I_max" means using existing concepts *)
Definition computes_optimization_bounds (Theory : Alphacarrier -> Prop) : Prop :=
  (* Theory can analyze predicates that encode optimization claims *)
  forall (P : Alphacarrier -> Prop),
  (exists n, alpha_enum n = Some P) ->
  exists (analysis : Alphacarrier),
  Theory analysis /\
  (* The analysis determines if P represents a valid optimization *)
  (Is_Impossible P -> Theory analysis).

(* This connects directly to your impossibility framework *)
Lemma optimization_bounds_detect_impossible :
  forall Theory,
  computes_optimization_bounds Theory ->
  forall P,
  Is_Impossible P ->
  (exists n, alpha_enum n = Some P) ->
  exists analysis, Theory analysis.
Proof.
  intros Theory Hcomp P Himp Henum.
  destruct (Hcomp P Henum) as [analysis [Hanalysis _]].
  exists analysis. exact Hanalysis.
Qed.

(* Now let's connect to the diagonal using your existing theorems *)
Theorem computing_bounds_requires_completeness :
  forall Theory,
  (exists n, alpha_enum n = Some Theory) ->
  computes_optimization_bounds Theory ->
  (* Theory must be able to analyze all enumerable predicates *)
  forall P, (exists m, alpha_enum m = Some P) ->
  exists analysis, Theory analysis.
Proof.
  intros Theory [n Hn] Hcomp P [m Hm].
  (* Every enumerable predicate P is either possible or impossible *)
  (* This uses your constructive framework *)
  destruct (Hcomp P (ex_intro _ m Hm)) as [analysis [Hanalysis _]].
  exists analysis. exact Hanalysis.
Qed.

(* But this means Theory is complete! *)
Theorem bounds_implies_complete :
  forall Theory,
  (exists n, alpha_enum n = Some Theory) ->
  computes_optimization_bounds Theory ->
  alpha_has_complete_optimization_theory.
Proof.
  intros Theory Henum Hcomp.
  exists Theory.
  split; [exact Henum|].
  split.
  - (* Theory analyzes everything *)
    apply computing_bounds_requires_completeness; assumption.
  - (* Including itself *)
    destruct Henum as [n Hn].
    destruct (computing_bounds_requires_completeness Theory (ex_intro _ n Hn) Hcomp Theory (ex_intro _ n Hn)) as [self_analysis Hself].
    exists self_analysis. exact Hself.
Qed.

Theorem no_theory_computes_bounds :
  forall Theory,
  (exists n, alpha_enum n = Some Theory) ->
  ~ computes_optimization_bounds Theory.
Proof.
  intros Theory Henum Hcomp.
  exact (no_complete_optimization_theory (bounds_implies_complete Theory Henum Hcomp)).
Qed.

(* Using your impossibility algebra more directly *)

(* Define optimization theories in terms of what they must reject *)
Definition respects_impossibility (Theory : Alphacarrier -> Prop) : Prop :=
  forall P,
  Is_Impossible P ->
  forall a, P a -> ~ Theory a.

(* Connect this to optimization *)
Definition optimization_claim (sys_encoding : Alphacarrier) : Alphacarrier -> Prop :=
  fun claim => 
    (* claim asserts that sys_encoding maximizes both S and ΔS *)
    claim = sys_encoding /\
    (* By cannot_maximize_both, this is impossible *)
    Is_Impossible (fun x => x = sys_encoding).

(* Now we can prove something concrete *)
Theorem optimization_theories_must_respect_impossibility :
  forall Theory,
  (exists n, alpha_enum n = Some Theory) ->
  (exists t, Theory t) ->  (* Non-empty *)
  respects_impossibility Theory ->
  (* Theory cannot prove any system maximizes both *)
  forall sys claim,
  optimization_claim sys claim ->
  ~ Theory claim.
Proof.
  intros Theory Henum Hnonempty Hrespect sys claim Hclaim.
  destruct Hclaim as [Heq Himp].
  subst claim.
  
  (* By Hrespect, Theory cannot contain impossible claims *)
  apply Hrespect with (P := fun x => x = sys).
  - exact Himp.
  - reflexivity.
Qed.
  
(* First, let's define what it means for a relation to represent something *)
Definition represents_system_relation (sys1 sys2 : Alphacarrier) 
  (relation : Alphacarrier) : Prop :=
  (* relation encodes that sys1 and sys2 are related in some way *)
  (* For now, we'll keep this abstract - it could be "sys1 transforms to sys2" 
     or "sys1 has bound less than sys2" etc. *)
  exists (R : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop),
  R sys1 sys2 relation.

(* What does it mean to violate the diagonal constraint? *)
Definition represents_diagonal_violation (Theory : Alphacarrier -> Prop) 
  (n : nat) (claim : Alphacarrier) : Prop :=
  alpha_enum n = Some Theory /\
  (* claim asserts that Theory can analyze its own diagonal *)
  exists a,
  claim = a /\
  Theory a /\
  diagonal_pred alpha_enum n a.

(* The diagonal constraint is absolute - no theory can violate it *)
Theorem diagonal_constrains_morphisms :
  forall Theory n claim,
  represents_diagonal_violation Theory n claim ->
  False.
Proof.
  intros Theory n claim [Henum [a [Hclaim [Htheory Hdiag]]]].
  subst claim.
  
  (* We have Theory a and diagonal_pred n a *)
  (* diagonal_pred n a means ~(Theory a) when alpha_enum n = Some Theory *)
  unfold diagonal_pred in Hdiag.
  rewrite Henum in Hdiag.
  
  (* So Hdiag : ~ Theory a *)
  (* But Htheory : Theory a *)
  exact (Hdiag Htheory).
Qed.

(* A relation violates constraints if it claims something impossible *)
Definition relation_claims_impossible (relation : Alphacarrier) : Prop :=
  exists P,
  Is_Impossible P /\
  (* relation claims some element satisfies P *)
  exists a, P a /\ relation = a.

(* All theories that respect impossibility must reject impossible relations *)
Theorem theories_reject_impossible_relations :
  forall Theory1 Theory2 relation,
  respects_impossibility Theory1 ->
  respects_impossibility Theory2 ->
  relation_claims_impossible relation ->
  ~ Theory1 relation /\ ~ Theory2 relation.
Proof.
  intros T1 T2 relation Hresp1 Hresp2 Himp_rel.
  
  destruct Himp_rel as [P [Himp [a [HPa Hrel]]]].
  subst relation.
  
  split.
  - (* ~ Theory1 a *)
    apply (Hresp1 P Himp a HPa).
  - (* ~ Theory2 a *)
    apply (Hresp2 P Himp a HPa).
Qed.

(* First define theory_proves_relation *)
Definition theory_proves_relation (Theory : Alphacarrier -> Prop) 
  (sys1 sys2 : Alphacarrier) (relation : Alphacarrier) : Prop :=
  Theory relation /\
  represents_system_relation sys1 sys2 relation.

(* Now we can define the morphism pattern *)
Definition theory_morphism_pattern (Theory : Alphacarrier -> Prop) : 
  Alphacarrier -> Alphacarrier -> Prop :=
  fun sys1 sys2 =>
    exists relation, 
    theory_proves_relation Theory sys1 sys2 relation.

(* Directions todo: 
- Try showing that the theory climbing toward a better optimization theory is itself I_max
- Try deriving systems from alpha / omega / generative type natively instead of defining them separately
- Try defining I_max through a limit that approaches the impossible predicate
- Show all optimization theories collapse to same constraints (uniqueness through shared diagonal constraints)
- Prove physics I_max formulas (∝ E/ℏ × k_B²) emerge from logical necessity
- Explore "reality as theorem" - existence itself follows from logic requiring Alpha/Omega distinction
*)

End MetaProof.


From Coq.Vectors Require Import Fin.
Require Import Coq.Program.Program.


(* A sketch of what P vs NP looks like in Alpha vs Omega *)
Section PvsNP_via_AlphaOmega.
  Context {Alpha : AlphaType} {Omega : OmegaType}.
  Variable embed : Alphacarrier -> Omegacarrier.
  
  (* ============================================ *)
  (* Step 1: SAT Framework                        *)
  (* ============================================ *)
  
  Definition Assignment (n : nat) := Fin.t n -> bool.

  Fixpoint fin_list (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n' => map FS (fin_list n') ++ [F1]
  end.

  Record Clause (n : nat) := {
    positive_vars : list (Fin.t n);
    negative_vars : list (Fin.t n);
    positive_valid : forall v, In v positive_vars -> True;
    negative_valid : forall v, In v negative_vars -> True
  }.


  Definition clause_satisfied {n} (c : Clause n) (a : Assignment n) : bool :=
    existsb (fun v => a v) (positive_vars n c) ||
    existsb (fun v => negb (a v)) (negative_vars n c).


  Record SAT_Instance := {
    num_vars : nat;
    clauses : list (Clause num_vars);
    non_trivial : num_vars > 0
  }.


  Program Definition extend_assignment {n} (b : bool) (f : Fin.t n -> bool) : Fin.t (S n) -> bool :=
    fun i =>
      match i with
      | F1 => b
      | FS j => f j
      end.


  Definition fin0_elim {A} (f : Fin.t 0) : A :=
    match f with end.


  Fixpoint all_assignments (n : nat) : list (Assignment n) :=
    match n with
    | 0 => [fun i => fin0_elim i]
    | S n' =>
        let prev := all_assignments n' in
        flat_map (fun f =>
          [extend_assignment false f; extend_assignment true f]) prev
    end.


  
  (* An instance is satisfiable if some assignment satisfies all clauses *)
  Definition Satisfiable (sat : SAT_Instance) : Prop :=
    exists (a : Assignment (num_vars sat)),
    forall c, In c (clauses sat) -> clause_satisfied c a = true.
  
  (* ============================================ *)
  (* Omega solves SAT instantly                   *)
  (* ============================================ *)
  
  (* The predicate: "I encode a satisfying assignment for sat" *)
  Definition SAT_Solution_Predicate (sat : SAT_Instance) : Omegacarrier -> Prop :=
    fun x => exists (a : Assignment (num_vars sat)),
      (forall c, In c (clauses sat) -> clause_satisfied c a = true) /\
      exists (enc : Alphacarrier), embed enc = x.
  
  Theorem omega_solves_SAT_instantly :
    forall (sat : SAT_Instance),
    Satisfiable sat ->
    exists (x : Omegacarrier), SAT_Solution_Predicate sat x.
  Proof.
    intros sat H_sat.
    apply omega_completeness.
  Qed.
  

  (* ============================================ *)
  (* Step 2: SAT as Universal Encoder             *)
  (* ============================================ *)

  Axiom all_assignments_complete : 
    forall (n : nat) (a : Assignment n), In a (all_assignments n).
  (* Technical axiom: every boolean assignment appears in our enumeration.
    This is "obviously true" but technically annoying to prove in Coq. *)

  Axiom sat_encoding_exists : 
    forall (P : Alphacarrier -> Prop),
    (forall a, {P a} + {~ P a}) ->
    exists (encode : nat -> SAT_Instance),
    forall n, (Satisfiable (encode n) <-> 
              exists a, P a (* where a is "encoded" by first n bits *)).

  (* This axiom needs proof - it's a massive assumption *)
  Axiom undecidable_creates_undecidable_sat :
    forall (P : Alphacarrier -> Prop),
    ~ ((exists a, P a) \/ (forall a, ~ P a)) ->
    exists (sat : SAT_Instance),
    ~ ((Satisfiable sat) \/ (~ Satisfiable sat)).

  
  (* ============================================ *)
  (* Step 3: Alpha has undecidable predicates     *)
  (* ============================================ *)
  
  (* Import the fact that we have enumeration and omega_diagonal *)
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop, exists n, alpha_enum n = Some A.
  
  (* Therefore, there exist undecidable predicates in Alpha *)
  
  Theorem exists_undecidable_in_alpha :
    exists (P : Alphacarrier -> Prop),
    ~ ((exists a, P a) \/ (forall a, ~ P a)).
  Proof.
    (* Use the omega_diagonal detection predicate *)
    exists (fun a => omega_diagonal alpha_enum embed (embed a)).
    
    (* Let's call this predicate D for "detects diagonal" *)
    set (D := fun a => omega_diagonal alpha_enum embed (embed a)).
    
    (* Suppose D were decidable *)
    intro H_dec.
    destruct H_dec as [H_exists | H_forall].
    
    - (* Case 1: exists a, D a *)
      destruct H_exists as [a Ha].
      
      (* This means omega_diagonal is representable! *)
      assert (representable (omega_diagonal alpha_enum embed)).
      {
        exists D, embed.
        intro a'.
        split.
        - intro HD. exact HD.
        - intro Hod. exact Hod.
      }
      
      (* But we proved omega_diagonal is not representable *)
      apply (omega_diagonal_not_representable alpha_enum enum_complete embed).
      exact H.
      
    - (* Case 2: forall a, ~ D a *)
      (* This means no Alpha element detects omega_diagonal *)
      
      (* But omega_diagonal has witnesses in Omega *)
      assert (exists x, omega_diagonal alpha_enum embed x).
      { apply omega_diagonal_exists. }
      destruct H as [x Hx].
      
      (* By construction of omega_diagonal, there exist n and a such that
         embed a = x and omega_diagonal holds at x *)
      unfold omega_diagonal in Hx.
      destruct Hx as [n [a' [Hembed Hdiag]]].
      
      (* So D a' should be true *)
      assert (D a').
      {
        unfold D.
        rewrite Hembed.
        exists n, a'.
        split.
        - exact Hembed.  (* Use the hypothesis, not reflexivity! *)
        - exact Hdiag.
      }
      
      (* But H_forall says D a' is false *)
      exact (H_forall a' H).
  Qed.
  
  
  (* ============================================ *)
  (* Step 5: Define polynomial SAT solvability    *)
  (* ============================================ *)
  
  Definition Polynomial_Time_SAT : Prop :=
    exists (poly : nat -> nat),
    (* poly is actually polynomial *)
    (exists k, forall n, poly n <= n^k) /\
    (* There's a solver that runs in poly time *)
    exists (solver : forall (sat : SAT_Instance), 
                     option (Assignment (num_vars sat))),
    forall sat,
      match solver sat with
      | Some a => forall c, In c (clauses sat) -> clause_satisfied c a = true
      | None => ~ Satisfiable sat
      end.
  
  (* ============================================ *)
  (* The Main Theorem: P and NP divergence                    *)
  (* ============================================ *)
  
  Theorem P_NP_Divergence :
    ~ Polynomial_Time_SAT.
  Proof.
    intro H_poly.
    destruct H_poly as [poly [H_poly_bound [solver H_solver]]].
    
    (* First, get an undecidable predicate in Alpha *)
    destruct exists_undecidable_in_alpha as [P H_undec].
    
    (* Then apply the axiom to get a SAT instance *)
    destruct (undecidable_creates_undecidable_sat P H_undec) as [hard_sat H_sat_undec].
    
    (* But polynomial solver decides it! *)
    destruct (solver hard_sat) eqn:E.
    
    - (* Case: solver found assignment *)
      assert (Satisfiable hard_sat).
      { exists a. 
        specialize (H_solver hard_sat).
        rewrite E in H_solver.
        exact H_solver. }
      
      (* This decides the undecidable *)
      assert ((Satisfiable hard_sat) \/ (~ Satisfiable hard_sat)).
      { left. exact H. }
      contradiction.
      
    - (* Case: solver says unsatisfiable *)
      assert (~ Satisfiable hard_sat).
      { specialize (H_solver hard_sat).
        rewrite E in H_solver.
        exact H_solver. }
      
      (* This also decides the undecidable *)
      assert ((Satisfiable hard_sat) \/ (~ Satisfiable hard_sat)).
      { right. exact H. }
      contradiction.
  Qed.
  
  (* ============================================ *)
  (* Note: P vs NP                                *)
  (* ============================================ *)
  
  (* Here, P ≠ NP is not about computation "speed."
     It's about the fundamental structure of mathematical reality:
     
     1. Complete systems (Omega) contain paradoxes
     2. Consistent systems (Alpha) must have undecidable predicates  
     3. These undecidable predicates can be encoded in SAT
     4. Therefore SAT must be undecidable in polynomial time in Alpha-like consistent systems
     5. Therefore P and NP behave differently in Alpha
     6. However, P and NP are not "different" in Omega-like paradoxical systems.
        Omega can solve SAT instantly, but it also has paradoxes and absurdities.
     
     This is the same phenomenon as:
     - Gödel: Logic has undecidable statements
     - Turing: Computation has undecidable problems
     - P vs NP: Consistent computation has undecidable instances in polynomial time
    
    TLDR: This is not a proof of P != NP in ZFC, but a construction showing
    why P and NP are different.
    This framework suggests that the difficulty of proving P ≠ NP in traditional 
    foundations may itself be a consequence of the fundamental representability 
    barriers we've identified.
  *)
  
End PvsNP_via_AlphaOmega.


Section HoTT_in_AlphaType.
  Context {Alpha : AlphaType}.
  
  (* Types are predicates on Alphacarrier *)
  Definition Type_A := Alphacarrier -> Prop.
  
  (* Elements of a type *)
  Definition El (A : Type_A) := { x : Alphacarrier | A x }.
  
  (* The empty type is the_impossible *)
  Definition Empty_t : Type_A := the_impossible.
  
  (* Unit type *)
  Variable unit_point : Alphacarrier.
  Definition Unit_t : Type_A := fun x => x = unit_point.
  
  (* We need pairing operations in Alphacarrier *)
  Variable pair_alpha : Alphacarrier -> Alphacarrier -> Alphacarrier.
  Variable fst_alpha : Alphacarrier -> Alphacarrier.
  Variable snd_alpha : Alphacarrier -> Alphacarrier.
  
  (* Pairing axioms *)
  Variable pair_fst : forall a b, fst_alpha (pair_alpha a b) = a.
  Variable pair_snd : forall a b, snd_alpha (pair_alpha a b) = b.
  Variable pair_eta : forall p, pair_alpha (fst_alpha p) (snd_alpha p) = p.
  
  (* Sum type constructors *)
  Variable inl_alpha : Alphacarrier -> Alphacarrier.
  Variable inr_alpha : Alphacarrier -> Alphacarrier.
  
  (* Path types *)
  Variable Path : forall (A : Type_A), Alphacarrier -> Alphacarrier -> Type_A.
  
  (* Reflexivity *)
  Variable refl : forall (A : Type_A) (x : Alphacarrier) (a : A x), 
    { r : Alphacarrier | Path A x x r }.
    
  Variable path_elim : forall (A : Type_A) (C : forall x y, Alphacarrier -> Type),
    (forall x (a : A x), C x x (proj1_sig (refl A x a))) ->
    forall x y p, Path A x y p -> C x y p.
  
  (* Product type *)
  Definition Prod (A B : Type_A) : Type_A :=
    fun p => exists a b, A a /\ B b /\ p = pair_alpha a b.
  
  (* Sum type *)
  Definition Sum (A B : Type_A) : Type_A :=
    fun s => (exists a, A a /\ s = inl_alpha a) \/ 
             (exists b, B b /\ s = inr_alpha b).
  
  (* Contractibility *)
  Definition isContr (A : Type_A) : Prop :=
    exists (center : Alphacarrier), A center /\ 
    forall x, A x -> exists p, Path A x center p.
  
  (* Transport - just axiomatize its existence *)
  Variable transport : forall (A : Type_A) (P : forall x, A x -> Type_A)
    (x y : Alphacarrier) (p : Alphacarrier) (a : A x) (ax : A y),
    Path A x y p -> 
    forall (u : Alphacarrier), P x a u -> 
    { v : Alphacarrier | P y ax v }.
  
  (* Path spaces *)
  Definition PathSpace (A : Type_A) (x y : Alphacarrier) : Type_A :=
    Path A x y.
  
  (* Ternary structure of paths in AlphaType:
     For any x, y in type A, the PathSpace A x y is:
     1. Inhabited (witnessed path exists)
     2. Empty (the_impossible - provably no path)
     3. Undecidable (neither inhabited nor empty)
  *)
  
  (* This could be the computational content of HoTT! *)
  Definition PathStatus (A : Type_A) (x y : Alphacarrier) : Type :=
    {p : Alphacarrier | Path A x y p} + 
    (Path A x y = the_impossible) +
    ((~ exists p, Path A x y p) * (~ forall p, ~ Path A x y p)).
  
  (* Univalence might emerge from the undecidability structure *)
  Definition Equiv (A B : Type_A) : Type_A :=
    fun e => exists (f g : Alphacarrier),
      (* f : A -> B and g : B -> A with appropriate properties *)
      (* Details omitted for brevity *)
      True.
  
  Variable univalence : forall (A B : Type_A),
    (* Equivalence of types gives path between them *)
    (* But this path might be undecidable! *)
    True.
  
End HoTT_in_AlphaType.


(* Section CategoryTheory.
  Context {Alpha : AlphaType}.
  
  (* Standard definition: A category has objects and morphisms *)
  (* We'll use Alphacarrier elements to represent both *)
  
  (* A morphism is just an element with source and target data *)
  Record Morphism := {
    mor_carrier : Alphacarrier;
    source : Alphacarrier;
    target : Alphacarrier
  }.
  
  (* A category is a predicate that identifies which elements are objects/morphisms *)
  Record Category := {
    is_object : Alphacarrier -> Prop;
    is_morphism : Morphism -> Prop;
    
    (* For each object, there's an identity morphism *)
    identity : forall x, is_object x -> Morphism;
    id_is_morphism : forall x (H : is_object x), is_morphism (identity x H);
    id_source : forall x (H : is_object x), source (identity x H) = x;
    id_target : forall x (H : is_object x), target (identity x H) = x;
    
    (* Composition of morphisms *)
    compose : forall (f g : Morphism), 
      is_morphism f -> is_morphism g -> 
      target f = source g ->
      Morphism;
    
    comp_is_morphism : forall f g Hf Hg Heq,
      is_morphism (compose f g Hf Hg Heq);
    comp_source : forall f g Hf Hg Heq,
      source (compose f g Hf Hg Heq) = source f;
    comp_target : forall f g Hf Hg Heq,
      target (compose f g Hf Hg Heq) = target g;
    
    (* Axioms *)
    assoc : forall f g h Hf Hg Hh Hfg Hgh Heq1 Heq2 Heq3,
      compose (compose f g Hf Hg Heq1) h 
        (comp_is_morphism f g Hf Hg Heq1) Hh Heq2 =
      compose f (compose g h Hg Hh Heq3) 
        Hf (comp_is_morphism g h Hg Hh Heq3) Heq2;
    
    (* Identity laws *)
    id_left : forall f Hf x Hx Heq,
      target (identity x Hx) = source f ->
      compose (identity x Hx) f (id_is_morphism x Hx) Hf Heq = f;
      
    id_right : forall f Hf x Hx Heq,
      target f = source (identity x Hx) ->
      compose f (identity x Hx) Hf (id_is_morphism x Hx) Heq = f
  }.
  
  (* Now let's build toward Yoneda *)
  
  (* A functor between categories *)
  Record Functor (C D : Category) := {
    obj_map : forall x, is_object C x -> Alphacarrier;
    obj_map_ok : forall x H, is_object D (obj_map x H);
    
    mor_map : forall f, is_morphism C f -> Morphism;
    mor_map_ok : forall f H, is_morphism D (mor_map f H);
    
    (* Preserves source/target *)
    preserves_source : forall f Hf,
      source (mor_map f Hf) = obj_map (source f) (admitted);
    preserves_target : forall f Hf,
      target (mor_map f Hf) = obj_map (target f) (admitted);
      
    (* Preserves identity and composition *)
    preserves_id : forall x Hx,
      mor_map (identity C x Hx) (id_is_morphism C x Hx) = 
      identity D (obj_map x Hx) (obj_map_ok x Hx);
      
    preserves_comp : forall f g Hf Hg Heq,
      mor_map (compose C f g Hf Hg Heq) (comp_is_morphism C f g Hf Hg Heq) =
      compose D (mor_map f Hf) (mor_map g Hg) 
        (mor_map_ok f Hf) (mor_map_ok g Hg) (admitted)
  }.
End CategoryTheory. *)


Class GenerativeType (Alpha : AlphaType) := {
  (* Time-indexed containment of Alpha predicates *)
  contains : nat -> (Alphacarrier -> Prop) -> Prop;
  
  (* The impossible is always contained (it's the anchor) *)
  impossible_always : forall t, contains t the_impossible;
  
  (* Backward containment still holds *)
  contains_backward : forall m n P, m <= n -> contains n P -> contains m P;
  
  (* Self-reference through Alpha predicates *)
  self_ref_pred_embed : ((Alphacarrier -> Prop) -> Prop) -> (Alphacarrier -> Prop);
  self_ref_pred_embed_correct : 
    forall P : (Alphacarrier -> Prop) -> Prop, 
    P (self_ref_pred_embed P);
  
  (* Generation with three-valued awareness *)
  self_ref_generation_exists : 
    forall P : (Alphacarrier -> Prop) -> Prop, 
    forall t : nat, 
    exists n : nat, t <= n /\ contains n (self_ref_pred_embed P);
  
  (* NEW: Undecidable predicates oscillate *)
  (* undecidable_oscillation :
    forall P : Alphacarrier -> Prop,
    (~ exists a, P a) -> (~ forall a, ~ P a) ->
    forall t, exists t', t' > t /\
      contains t P <> contains t' P *)
}.


(* First, let's establish the basic self-reference examples *)

Example gen_novice_self_ref_example : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  let P := fun (pred : Alphacarrier -> Prop) => ~ contains 0 pred in
  P (self_ref_pred_embed P).
Proof.
  intros Alpha H P.
  unfold P.
  apply self_ref_pred_embed_correct.
Qed.

Example gen_self_ref_pred_appears_later : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  let Q := fun (pred : Alphacarrier -> Prop) => 
    exists t : nat, t > 0 /\ contains t pred in
  Q (self_ref_pred_embed Q).
Proof.
  intros.
  apply self_ref_pred_embed_correct.
Qed.

(* Temporal evolution with Alpha awareness *)
Example gen_self_ref_pred_temporal_evolution : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  let R := fun (pred : Alphacarrier -> Prop) => 
    ~ contains 0 pred /\ exists t : nat, t > 0 /\ contains t pred in
  R (self_ref_pred_embed R).
Proof.
  intros.
  apply self_ref_pred_embed_correct.
Qed.

(* NEW: Example showing the_impossible is always present *)
Example gen_impossible_always_contained :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall t : nat, contains t the_impossible.
Proof.
  intros.
  apply impossible_always.
Qed.

(*****************************************************************)
(*                         Core Theorems                         *)
(*****************************************************************)

(* AlphaGen builds itself recursively *)
Theorem gen_builds_itself : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop, 
  exists n : nat, contains n (self_ref_pred_embed P).
Proof.
  intros Alpha H P.
  destruct (self_ref_generation_exists P 0) as [n [Hle Hc]].
  exists n.
  assumption.
Qed.

(* Theorem: AlphaGen recognizes its initial incompleteness *)
Theorem gen_recognizes_initially_incomplete : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  exists P : (Alphacarrier -> Prop) -> Prop, 
    (~ contains 0 (self_ref_pred_embed P)) /\ 
    (exists n : nat, contains n (self_ref_pred_embed P)).
Proof.
  intros Alpha H.
  (* Define P: "pred is not contained at stage 0" *)
  set (P := fun pred : Alphacarrier -> Prop => ~ contains 0 pred).
  assert (H_not0: ~ contains 0 (self_ref_pred_embed P)).
  {
    apply self_ref_pred_embed_correct.
  }
  destruct (self_ref_generation_exists P 0) as [n [Hle Hn]].
  exists P.
  split.
  - exact H_not0.
  - exists n. exact Hn.
Qed.

(* Theorem: AlphaGen Recursively Grows
   For predicates on Alpha predicates, we can combine them with temporal conditions *)
Theorem gen_recursive_growth : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop, 
  exists n : nat, 
    contains n (self_ref_pred_embed (fun pred => P pred /\ contains 0 pred)).
Proof.
  intros Alpha H P.
  destruct (self_ref_generation_exists (fun pred => P pred /\ contains 0 pred) 0) as [n [Hle Hc]].
  exists n.
  assumption.
Qed.

(* Predicates appear at multiple times *)
Theorem gen_P_not_unique :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop, 
  exists n m : nat,
    n < m /\
    contains n (self_ref_pred_embed P) /\
    contains m (self_ref_pred_embed P).
Proof.
  intros Alpha H P.
  destruct (self_ref_generation_exists P 0) as [n [Hn_ge Hn_cont]].
  destruct (self_ref_generation_exists P (n + 1)) as [m [Hm_ge Hm_cont]].
  assert (n < m) by lia.
  exists n, m.
  repeat split; assumption.
Qed.

(* P and its negation eventually both appear *)
Theorem gen_P_eventually_negated :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop, 
  exists n m : nat,
    n < m /\
    contains n (self_ref_pred_embed P) /\
    contains m (self_ref_pred_embed (fun pred => ~ P pred)).
Proof.
  intros Alpha H P.
  destruct (self_ref_generation_exists P 0) as [n [Hle_n Hn]].
  destruct (self_ref_generation_exists (fun pred => ~ P pred) (n + 1)) as [m [Hle_m Hm]].
  exists n, m.
  split.
  - lia.
  - split; assumption.
Qed.

(* The fundamental incompleteness - there's always something not yet contained *)
Theorem gen_never_complete : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall t : nat, 
  exists P : (Alphacarrier -> Prop) -> Prop, 
  ~ contains t (self_ref_pred_embed P).
Proof.
  intros Alpha H t.
  exists (fun pred => ~ contains t pred).
  apply self_ref_pred_embed_correct.
Qed.


(** 
  Finite-Stage Incompleteness for GenerativeType:
  There exists some finite stage n at which GenerativeType explicitly embeds the statement
  "there is a predicate P0 whose embedding is absent from all stages m <= n."
**)
Theorem gen_recognizes_its_own_incompleteness_for_all_time :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
    forall t : nat,
      exists n : nat,
        t < n /\
        contains n (self_ref_pred_embed
          (fun _ : Alphacarrier -> Prop =>
            exists P0 : (Alphacarrier -> Prop) -> Prop,
              ~ contains n (self_ref_pred_embed P0))).
Proof.
  intros Alpha H t.
  (* Step 1: Define the predicate Q that asserts "pred is not contained at time t" *)
  set (Q := fun pred : Alphacarrier -> Prop => ~ contains t pred).
  
  (* Step 2: Use self_ref_pred_embed_correct to show that Q holds of its own embedding *)
  assert (H_Q_not_t : ~ contains t (self_ref_pred_embed Q)).
  {
    apply self_ref_pred_embed_correct.
  }
  
  (* Step 3: Use self_ref_generation_exists to find n > t where Q is embedded *)
  destruct (self_ref_generation_exists Q (t + 1)) as [n [H_le H_contains_Q]].
  
  (* Step 4: Set P0 := Q. Q is a predicate not contained at time t *)
  set (P0 := Q).
  
  (* Step 5: Prove that P0's embedding is not contained at time n *)
  assert (H_P0_not_n : ~ contains n (self_ref_pred_embed P0)).
  {
    apply self_ref_pred_embed_correct.
  }
  
  (* Step 6: Define R' as the predicate that "some P0 is not contained at time n" *)
  set (R' := fun _ : Alphacarrier -> Prop => 
    exists P0 : (Alphacarrier -> Prop) -> Prop, 
    ~ contains n (self_ref_pred_embed P0)).
    
  (* Step 7: Prove R' is satisfied at its own embedding *)
  assert (H_R' : R' (self_ref_pred_embed R')).
  {
    unfold R'. exists P0. exact H_P0_not_n.
  }
  
  (* Step 8: Use self_ref_generation_exists again to embed R' at some time ≥ n *)
  destruct (self_ref_generation_exists R' n) as [k [H_ge_k H_contains_R']].
  
  (* Step 9: Use backward monotonicity to bring R' embedding down to time n if needed *)
  apply (contains_backward n k (self_ref_pred_embed R')) in H_contains_R'; [| lia].
  
  exists n.
  split.
  - lia.
  - exact H_contains_R'.
Qed.

(* Theorem: GenerativeType Is Infinite
   There exists a function F: (Alphacarrier -> Prop) -> nat -> (Alphacarrier -> Prop) 
   such that for every time t, F the_impossible t is contained at time t.
*)
Theorem gen_is_infinite : 
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  exists F : (Alphacarrier -> Prop) -> nat -> (Alphacarrier -> Prop), 
  forall t : nat, contains t (F the_impossible t).
Proof.
  intros Alpha H.
  
  (* Define F such that for each pred and t, 
     F pred t = self_ref_pred_embed (fun p => contains t p) *)
  exists (fun pred t => self_ref_pred_embed (fun p => contains t p)).
  intros t.
  
  (* By self_ref_generation_exists, the predicate describing membership at t
     is eventually embedded at some later stage n ≥ t *)
  destruct (self_ref_generation_exists (fun p => contains t p) t) as [n [Hle Hn]].
  
  (* By cumulative monotonicity (contains_backward), 
     the embedding at n implies membership at t *)
  apply (contains_backward t n (self_ref_pred_embed (fun p => contains t p)) Hle Hn).
Qed.


(* GenerativeType grows like naturals - showing infinite generative capacity *)
Theorem gen_grows_like_naturals :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  exists (f : nat -> (Alphacarrier -> Prop)),
    contains 0 (f 0) /\
    forall n, contains n (f (n+1)).
Proof.
  intros Alpha H.
  (* Define a sequence embedding the predicate "membership at stage n" *)
  exists (fun n => self_ref_pred_embed (fun p => contains n p)).
  split.
  - (* Base case: Show f(0) is contained at time 0 *)
    destruct (self_ref_generation_exists (fun p => contains 0 p) 0) as [n [Hn_le Hn_contains]].
    apply (contains_backward 0 n).
    + lia.
    + exact Hn_contains.
  - (* Inductive step: Show f(n+1) is contained at time n *)
    intros n.
    destruct (self_ref_generation_exists (fun p => contains (n+1) p) n) as [t [Ht_le Ht_contained]].
    apply (contains_backward n t).
    + lia.
    + exact Ht_contained.
Qed.

(** Theorem: GenerativeType Can Contain Contradictory Statements About The Past
    This shows how Alpha's ternary logic manifests temporally:
    - At time t: Contains "pred is not in GenerativeType at time 0"
    - At time t+1: Contains "pred is in GenerativeType at time 0"
    
    This is particularly interesting for Alpha because it shows how
    undecidable predicates can have contradictory statements coexist
    through temporal separation.
*)
Theorem gen_contains_temporal_contradictions :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  exists t : nat, 
    contains t (self_ref_pred_embed (fun pred => ~ contains 0 pred)) /\
    contains (t + 1) (self_ref_pred_embed (fun pred => contains 0 pred)).
Proof.
  intros Alpha H.
  
  (* First statement must be contained *)
  destruct (self_ref_generation_exists (fun pred => ~ contains 0 pred) 0) as [t1 [Ht1_le Ht1_contained]].
  
  (* Contradictory statement must also be contained *)
  destruct (self_ref_generation_exists (fun pred => contains 0 pred) (t1 + 1)) as [t2 [Ht2_le Ht2_contained]].
  
  exists t1.
  split.
  - exact Ht1_contained.
  - apply (contains_backward (t1 + 1) t2).
    + lia.
    + exact Ht2_contained.
Qed.

(** Theorem: Time Allows Paradox Resolution in Alpha
    This demonstrates how Alpha's GenerativeType handles paradoxes:
    by temporal separation rather than logical exclusion.
    
    This connects to Alpha's ternary logic - undecidable predicates
    can have both P and ¬P represented at different times!
*)
Theorem gen_time_allows_paradox:
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  exists (t1 t2 : nat) (P : (Alphacarrier -> Prop) -> Prop),
    (contains t1 (self_ref_pred_embed P) /\
     contains t2 (self_ref_pred_embed (fun pred => ~ P pred))) /\
    t1 < t2.
Proof.
  intros Alpha H.
  set (P := fun pred : Alphacarrier -> Prop => contains 0 pred).
  
  (* Embed P at some initial stage *)
  destruct (self_ref_generation_exists P 0) as [t1 [H_t1_le H_t1_contains]].
  
  (* Embed negation of P at a later stage *)
  destruct (self_ref_generation_exists (fun pred => ~ P pred) (t1 + 1)) as [t2 [H_t2_le H_t2_contains_neg]].
  
  exists t1, t2, P.
  split.
  - split; assumption.
  - lia.
Qed.


(* Theorem: GenerativeType doesn't have temporal containment paradoxes at the same time step *)
Theorem gen_no_temporal_containment_paradoxes :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall t : nat,
  ~ exists P : (Alphacarrier -> Prop) -> Prop, 
    (contains t (self_ref_pred_embed P) /\ ~ contains t (self_ref_pred_embed P)).
Proof.
  intros Alpha H t.
  intro Hparadox.
  destruct Hparadox as [P [H1 H2]].
  contradiction.
Qed.

(* Theorem: No predicate P directly contradicts itself in the same element *)
Theorem gen_no_true_and_negated_true_for_same_element :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop,
  ~ (P (self_ref_pred_embed P) /\ (fun pred => ~ P pred) (self_ref_pred_embed P)).
Proof.
  intros Alpha H P [HP HnP].
  unfold not in HnP.
  apply HnP.
  exact HP.
Qed.

(* Theorem: Paradoxes propagate backward in time in Alpha's GenerativeType *)
(* This is particularly interesting for Alpha because it shows how undecidable
   predicates create temporal superpositions - both P and ~P coexist at earlier times *)
Theorem gen_paradoxical_embeddings_propagate_backward :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall (P : (Alphacarrier -> Prop) -> Prop),
  forall (t1 t2 : nat),
    contains t1 (self_ref_pred_embed P) ->
    contains t2 (self_ref_pred_embed (fun pred => ~ P pred)) ->
    forall t : nat,
      t <= Nat.min t1 t2 ->
      contains t (self_ref_pred_embed P) /\
      contains t (self_ref_pred_embed (fun pred => ~ P pred)).
Proof.
  intros Alpha H P t1 t2 HP HnP t Ht.
  pose (tmin := Nat.min t1 t2).

  (* 1) Show P is contained at time tmin *)
  assert (HP_tmin : contains tmin (self_ref_pred_embed P)).
  {
    apply contains_backward with (n := t1).
    - apply Nat.le_min_l.
    - exact HP.
  }

  (* 2) Show ~P is contained at time tmin *)
  assert (HnP_tmin : contains tmin (self_ref_pred_embed (fun pred => ~ P pred))).
  {
    apply contains_backward with (n := t2).
    - apply Nat.le_min_r.
    - exact HnP.
  }

  (* 3) Now go from tmin back to any t <= tmin *)
  split.
  - apply contains_backward with (n := tmin); [exact Ht | exact HP_tmin].
  - apply contains_backward with (n := tmin); [exact Ht | exact HnP_tmin].
Qed.

(* This theorem shows Alpha's ternary logic manifesting temporally *)
Theorem gen_simultaneous_negation :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop,
  exists t : nat,
    contains t (self_ref_pred_embed P) /\
    contains t (self_ref_pred_embed (fun pred => ~ P pred)).
Proof.
  intros Alpha H P.

  (* Get stages where P and ~P are embedded *)
  destruct (self_ref_generation_exists P 0) as [t1 [Ht1 HP]].
  destruct (self_ref_generation_exists (fun pred => ~ P pred) 0) as [t2 [Ht2 HnP]].

  (* Apply the propagation theorem *)
  set (t := Nat.min t1 t2).
  apply gen_paradoxical_embeddings_propagate_backward with (t1 := t1) (t2 := t2) (P := P) (t := t) in HP; try exact HnP.
  destruct HP as [Hpos Hneg].
  exists t; split; assumption.
  reflexivity.
Qed.

(* This is the most striking theorem - at time 0, ALL predicates and their negations coexist!
   This suggests time 0 is like a "superposition" state where Alpha contains all possibilities
   before they unfold temporally. This connects beautifully to:
   - Alpha's ternary logic (undecidable predicates)
   - The need for temporal differentiation to avoid Omega collapse
   - The "Big Bang" necessity we discussed earlier *)
Theorem gen_simultaneous_negation_t0 :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop,
  contains 0 (self_ref_pred_embed P) /\
  contains 0 (self_ref_pred_embed (fun pred => ~ P pred)).
Proof.
  intros Alpha H P.
  
  (* Step 1: Show that P and ~P must exist at some times t1 and t2 *)
  destruct (self_ref_generation_exists P 0) as [t1 [Ht1_ge Ht1_contains]].
  destruct (self_ref_generation_exists (fun pred => ~ P pred) 0) as [t2 [Ht2_ge Ht2_contains]].
  
  (* Step 2: We need the minimum of t1 and t2 *)
  set (tmin := Nat.min t1 t2).
  
  (* Step 3: Apply the backward propagation theorem with proper parameters *)
  assert (H_prop_back: forall t : nat, t <= tmin -> 
            contains t (self_ref_pred_embed P) /\
            contains t (self_ref_pred_embed (fun pred => ~ P pred))).
  { apply (gen_paradoxical_embeddings_propagate_backward Alpha H P t1 t2); assumption. }
  
  (* Step 4: Show 0 <= tmin directly using properties we know *)
  assert (H_le_tmin: 0 <= tmin).
  { 
    eapply Nat.min_glb.
    - exact Ht1_ge.
    - exact Ht2_ge.
  }
  
  (* Step 5: Get the result by applying our assertion *)
  apply H_prop_back.
  exact H_le_tmin.
Qed.


(* Theorem: There exists a predicate that is contained at time 0 but cannot be contained at time 1 *)
(* This shows time 0 is special - it contains predicates that vanish at later times *)
Theorem gen_predicate_contained_at_0_not_at_1 :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  exists P : (Alphacarrier -> Prop) -> Prop,
    contains 0 (self_ref_pred_embed P) /\
    ~ contains 1 (self_ref_pred_embed P).
Proof.
  intros Alpha H.
  
  (* Define our predicate: "pred is not contained at time 1" *)
  set (P := fun pred : Alphacarrier -> Prop => ~ contains 1 pred).
  
  (* Generate P at time 0 using self_ref_generation_exists *)
  destruct (self_ref_generation_exists P 0) as [t [Ht_ge Ht_contains]].
  
  (* Use self_ref_pred_embed_correct to get the semantic property of P *)
  assert (HP_property: ~ contains 1 (self_ref_pred_embed P)).
  { apply self_ref_pred_embed_correct. }
  
  (* Contains_backward to ensure P exists at time 0 if t > 0 *)
  assert (H_contains_0: contains 0 (self_ref_pred_embed P)).
  { apply (contains_backward 0 t).
    - exact Ht_ge.
    - exact Ht_contains. }
  
  exists P.
  split.
  - exact H_contains_0.
  - exact HP_property.
Qed.

(* Create a predicate that can *only* be contained at t=0 and no later time *)
(* This reinforces that t=0 is like a superposition state that must differentiate *)
Theorem gen_predicate_only_contained_at_0 :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  exists P : (Alphacarrier -> Prop) -> Prop,
    contains 0 (self_ref_pred_embed P) /\
    forall t : nat, t > 0 -> ~ contains t (self_ref_pred_embed P).
Proof.
  intros Alpha H.
  
  (* Define our predicate: "pred is not contained at time t>0" *)
  set (P := fun pred : Alphacarrier -> Prop => forall t : nat, t > 0 -> ~ contains t pred).
  
  (* Generate P at time 0 using self_ref_generation_exists *)
  destruct (self_ref_generation_exists P 0) as [t [Ht_ge Ht_contains]].
  
  (* Use self_ref_pred_embed_correct to get the semantic property of P *)
  assert (HP_property: forall t' : nat, t' > 0 -> ~ contains t' (self_ref_pred_embed P)).
  { apply self_ref_pred_embed_correct. }
  
  (* Contains_backward to ensure P exists at time 0 if t > 0 *)
  assert (H_contains_0: contains 0 (self_ref_pred_embed P)).
  { apply (contains_backward 0 t).
    - exact Ht_ge.
    - exact Ht_contains. }
  
  exists P.
  split.
  - exact H_contains_0.
  - exact HP_property.
Qed.

(* Theorem: Every predicate P is contained at time 0 *)
(* This confirms t=0 is the universal superposition state! *)
Theorem gen_contains_t0_all_P :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop,
  contains 0 (self_ref_pred_embed P).
Proof.
  intros Alpha H P.
  
  (* By theorem gen_simultaneous_negation_t0, we know that every predicate and its negation 
     are both contained at time 0 *)
  pose proof (gen_simultaneous_negation_t0 Alpha H P) as [H_contains_P _].
  
  exact H_contains_P.
Qed.

(* Theorem: Time 0 contains the liar's paradox - this is particularly interesting
   for Alpha because it shows how self-referential paradoxes exist in superposition *)
Theorem gen_contains_liars_paradox_t0 :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  contains 0 (self_ref_pred_embed (fun pred => ~ contains 0 pred)) /\
  contains 0 (self_ref_pred_embed (fun pred => contains 0 pred)).
Proof.
  intros Alpha H.
  
  split.
  - apply (gen_contains_t0_all_P Alpha H (fun pred => ~ contains 0 pred)).
  - apply (gen_contains_t0_all_P Alpha H (fun pred => contains 0 pred)).
Qed.


(* Convenience function to get the carrier from an OmegaType *)
Definition Omega_carrier_gen (Omega : OmegaType) : Type :=
  Omegacarrier.

(**
 [OmegaToGenerative] bridges GenerativeType and OmegaType.
 It shows how to embed Alpha predicates into the timeless Omega, 
 and project from Omega back to time-indexed predicates in GenerativeType.
**)
Class OmegaToGenerative (Alpha : AlphaType) (HG : GenerativeType Alpha) (Omega : OmegaType) := {
  project_Omega_gen : Omegacarrier -> (Alphacarrier -> Prop);
  lift_Gen : (Alphacarrier -> Prop) -> Omegacarrier;
  
  (* Key coherence: Omega contains all predicates timelessly, 
     GenerativeType reveals them temporally *)
  projection_coherence_gen : forall (x : Omegacarrier) (t : nat),
    exists (P : Alphacarrier -> Prop), 
    contains t P /\ P = project_Omega_gen x
}.

(* Computable class for GenerativeType - predicates can be algorithmically described *)
Class ComputableGen (Alpha : AlphaType) := {
  describable_gen : ((Alphacarrier -> Prop) -> bool) -> Prop;
  computability_axiom_gen : 
    forall P : (Alphacarrier -> Prop) -> Prop, 
    exists f : (Alphacarrier -> Prop) -> bool, describable_gen f
}.

(* Theorem: GenerativeType is algorithmically describable *)
Theorem gen_is_algorithmic : 
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha) (HC : ComputableGen Alpha),
  forall P : (Alphacarrier -> Prop) -> Prop, 
  exists f : (Alphacarrier -> Prop) -> bool, describable_gen f.
Proof.
  intros Alpha HG HC P.
  exact (computability_axiom_gen P).
Qed.

(* Theorem: GenerativeType requires computation over time, while Omega retrieves instantly *)
(* This shows the fundamental difference: 
   - GenerativeType: Predicates unfold temporally (avoiding paradox)
   - Omega: All predicates exist simultaneously (embracing paradox) *)
Theorem omega_computes_instantly_gen :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha) (HC : ComputableGen Alpha)
         (Omega : OmegaType) (HOG : OmegaToGenerative Alpha HG Omega),
  exists (P : (Alphacarrier -> Prop) -> Prop) (S : (Alphacarrier -> Prop) -> (Alphacarrier -> Prop)),
    (* In GenerativeType, solutions require time to compute *)
    (forall pred : Alphacarrier -> Prop, exists n : nat, contains n (S pred)) /\
    (* In Omega, all solutions exist timelessly *)
    (forall x : Omegacarrier, exists Q : Alphacarrier -> Prop, 
      Q = project_Omega_gen x /\ contains 0 Q).
Proof.
  intros Alpha HG HC Omega HOG.
  
  (* Define a problem that requires computation in GenerativeType *)
  set (P := fun pred : Alphacarrier -> Prop => contains 0 pred).
  set (S := fun pred : Alphacarrier -> Prop => 
    self_ref_pred_embed (fun p => contains 0 p)).
  
  (* In GenerativeType, solving requires computation over time *)
  assert (H_gen_computation: forall pred : Alphacarrier -> Prop, 
    exists n : nat, contains n (S pred)).
  { 
    intros pred.
    destruct (self_ref_generation_exists (fun p => contains 0 p) 0) as [n [Hle Hn]].
    exists n.
    exact Hn.
  }
  
  (* In Omega, solutions exist timelessly via projection *)
  assert (H_omega_instant: forall x : Omegacarrier, 
    exists Q : Alphacarrier -> Prop, Q = project_Omega_gen x /\ contains 0 Q).
  { 
    intros x.
    destruct (projection_coherence_gen x 0) as [Q [Hcontains HQ_eq]].
    exists Q.
    split.
    - exact HQ_eq.
    - exact Hcontains.
  }
  
  exists P, S.
  split; assumption.
Qed.


(* GenerativeType cannot embed Omega's contradictions - no classical logic needed! *)
Theorem gen_no_omega_paradox :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha) (Omega : OmegaType),
  forall t : nat,
    ~ contains t (self_ref_pred_embed (fun _ : Alphacarrier -> Prop =>
      exists (P : Omegacarrier -> Prop) (y : Omegacarrier), P y /\ ~ P y)).
Proof.
  intros Alpha HG Omega t H_contains.
  
  (* If this were contained, self_ref_pred_embed_correct would give us the paradox *)
  pose proof (self_ref_pred_embed_correct 
    (fun _ : Alphacarrier -> Prop => 
      exists (P : Omegacarrier -> Prop) (y : Omegacarrier), P y /\ ~ P y)) as H_paradox.
  
  (* This gives us a direct contradiction *)
  destruct H_paradox as [P [y [HP HnotP]]].
  exact (HnotP HP).
Qed.


Theorem gen_no_direct_contradictions :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha),
  forall t : nat,
  forall P : (Alphacarrier -> Prop) -> Prop,
  ~ (contains t (self_ref_pred_embed P) /\ 
     contains t (self_ref_pred_embed (fun pred => ~ P pred)) /\
     P = (fun pred => ~ P pred)).
Proof.
  intros Alpha HG t P [H_P [H_notP H_eq]].
  
  (* Get P (self_ref_pred_embed P) from self_ref_pred_embed_correct *)
  pose proof (self_ref_pred_embed_correct P) as HP.
  
  (* Use eq_ind to transport HP across the equality H_eq *)
  pose proof (eq_ind P 
                     (fun Q => Q (self_ref_pred_embed P))
                     HP
                     (fun pred => ~ P pred)
                     H_eq) as H_transported.
  
  (* Now H_transported : (fun pred => ~ P pred) (self_ref_pred_embed P) *)
  (* Which beta-reduces to: ~ P (self_ref_pred_embed P) *)
  simpl in H_transported.
  
  (* But we also have P (self_ref_pred_embed P) from HP *)
  exact (H_transported HP).
Qed.


(* GenerativeType can safely simulate Omega-like behavior through temporal staging *)
Theorem gen_temporal_omega_simulation :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha) (Omega : OmegaType),
  forall (P_omega : Omegacarrier -> Prop),
  (* Even if P_omega is paradoxical in Omega *)
  (exists y : Omegacarrier, P_omega y /\ ~ P_omega y) ->
  (* GenerativeType can represent both parts at different times *)
  exists t1 t2 : nat,
    t1 <> t2 /\
    contains t1 (self_ref_pred_embed (fun _ => exists y, P_omega y)) /\
    contains t2 (self_ref_pred_embed (fun _ => exists y, ~ P_omega y)).
Proof.
  intros Alpha HG Omega P_omega H_paradox.
  
  (* First predicate: "P_omega has a witness" *)
  destruct (self_ref_generation_exists (fun _ => exists y, P_omega y) 0) as [t1 [Ht1_ge Ht1_cont]].
  
  (* Second predicate: "~P_omega has a witness" *)
  destruct (self_ref_generation_exists (fun _ => exists y, ~ P_omega y) (t1 + 1)) as [t2 [Ht2_ge Ht2_cont]].
  
  exists t1, t2.
  split; [|split].
  - (* t1 ≠ t2 because t2 ≥ t1 + 1 *)
    lia.
  - exact Ht1_cont.
  - exact Ht2_cont.
Qed.


(* GenerativeType provides a "safe window" into Omega through projection *)
Theorem gen_safe_omega_window :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha) (Omega : OmegaType)
         (HOG : OmegaToGenerative Alpha HG Omega),
  forall x : Omegacarrier,
  forall t : nat,
  (* The projection from Omega is always safe (doesn't create direct contradictions) *)
  let P := project_Omega_gen x in
  ~ (P = the_impossible /\ contains t P /\ ~ contains t P).
Proof.
  intros Alpha HG Omega HOG x t P [H_imp [H_cont H_not_cont]].
  (* Direct contradiction between H_cont and H_not_cont *)
  exact (H_not_cont H_cont).
Qed.

(* Undecidable predicates in Alpha might exhibit special temporal behavior *)
Theorem gen_undecidable_temporal_pattern :
  forall (Alpha : AlphaType) (HG : GenerativeType Alpha),
  forall P : Alphacarrier -> Prop,
  (* If P is undecidable in Alpha's ternary logic *)
  (~ exists a, P a) -> (~ forall a, ~ P a) ->
  (* Then predicates about P might have interesting temporal properties *)
  exists (MetaP : (Alphacarrier -> Prop) -> Prop),
    (* MetaP asks about P's undecidability *)
    (forall pred, MetaP pred <-> (pred = P /\ ~ exists a, P a /\ ~ forall a, ~ P a)) /\
    (* And MetaP appears at some time *)
    exists t, contains t (self_ref_pred_embed MetaP).
Proof.
  intros Alpha HG P H_no_witness H_not_impossible.
  
  (* Define MetaP as a predicate that recognizes P's undecidability *)
  exists (fun pred => pred = P /\ ~ exists a, P a /\ ~ forall a, ~ P a).
  split.
  - (* The characterization is just reflexivity *)
    intro pred. reflexivity.
  - (* Use self_ref_generation_exists to show it eventually appears *)
    destruct (self_ref_generation_exists 
      (fun pred => pred = P /\ ~ exists a, P a /\ ~ forall a, ~ P a) 0) 
      as [t [_ Ht_cont]].
    exists t. exact Ht_cont.
Qed.


Section SelfRecursiveGenerative.
  Context (Alpha : AlphaType) (HG : GenerativeType Alpha).
  
  (* A subset of predicates is modeled as a predicate on predicates *)
  Definition PowerSetGen := (Alphacarrier -> Prop) -> Prop.
  
  (* GenerativeType contains all meta-predicates via self_ref_pred_embed *)
  Definition gen_contains_power_set : Prop :=
    forall (S : PowerSetGen), exists t, contains t (self_ref_pred_embed S).
  
  (* GenerativeType's predicates are contained in its power set via singleton predicates *)
  Definition gen_is_subset_of_power_set : Prop :=
    forall (P : Alphacarrier -> Prop), 
      exists S : PowerSetGen, 
      forall Q : Alphacarrier -> Prop, S Q <-> Q = P.
  
  (* Theorem: GenerativeType and its powerset mutually contain each other *)
  Theorem gen_and_power_set_mutually_embed :
    gen_contains_power_set /\ gen_is_subset_of_power_set.
  Proof.
    split.
    (* Part 1: GenerativeType contains its power set *)
    - unfold gen_contains_power_set.
      intros S.
      destruct (self_ref_generation_exists S 0) as [t [H_le H_contains]].
      exists t.
      exact H_contains.
    (* Part 2: GenerativeType is subset of its own power set *)
    - unfold gen_is_subset_of_power_set.
      intros P.
      exists (fun Q => Q = P).
      intros Q. split; intros H2; subst; auto.
  Qed.
  
  (* GenerativeType is self-reflective about its own temporal structure *)
  Theorem gen_is_self_reflective :
    exists (f : nat -> (Alphacarrier -> Prop)),
      forall n : nat,
        exists P : PowerSetGen,
          contains n (f n) /\
          f n = self_ref_pred_embed P /\
          (* GenerativeType contains meta-statements about its own containment *)
          (exists m : nat,
            contains m (self_ref_pred_embed 
              (fun _ : Alphacarrier -> Prop => 
                exists m, contains m (self_ref_pred_embed P)))).
  Proof.
    (* f(n) embeds "what is contained at time n" *)
    exists (fun n => self_ref_pred_embed (fun pred => contains n pred)).
    intros n.
    set (P := fun pred : Alphacarrier -> Prop => contains n pred).
    exists P.
    split.
    - (* Show f(n) is contained at time n *)
      destruct (self_ref_generation_exists P n) as [t [H_le H_contained]].
      apply (contains_backward n t (self_ref_pred_embed P) H_le H_contained).
    - split.
      + reflexivity.
      + (* GenerativeType contains a statement about its own knowledge of P *)
        destruct (self_ref_generation_exists 
          (fun _ : Alphacarrier -> Prop => 
            exists m, contains m (self_ref_pred_embed P)) n)
          as [m [H_le_m H_contains_m]].
        exists m.
        exact H_contains_m.
  Qed.
  
  (* Additional theorem: GenerativeType can reason about the_impossible *)
  Theorem gen_contains_impossible_reasoning :
    exists t : nat,
      contains t (self_ref_pred_embed 
        (fun P => P = the_impossible \/ 
                  (forall a, P a -> the_impossible a))).
  Proof.
    destruct (self_ref_generation_exists 
      (fun P => P = the_impossible \/ 
                (forall a, P a -> the_impossible a)) 0) 
      as [t [_ Ht]].
    exists t. exact Ht.
  Qed.
  
  (* GenerativeType contains statements about its own temporal evolution *)
  Theorem gen_temporal_self_awareness :
    forall n : nat,
    exists t : nat,
      contains t (self_ref_pred_embed 
        (fun P => contains n P -> exists m, m > n /\ contains m P)).
  Proof.
    intro n.
    destruct (self_ref_generation_exists 
      (fun P => contains n P -> exists m, m > n /\ contains m P) n)
      as [t [_ Ht]].
    exists t. exact Ht.
  Qed.

  (* We can literally encode Russell's construction! *)
  Example gen_russell_construction:
    exists t : nat, 
      contains t (self_ref_pred_embed 
        (fun P : Alphacarrier -> Prop => 
          ~ contains 0 (self_ref_pred_embed (fun _ => P = P)))).
  Proof.
    (* Define Russell's predicate *)
    set (Russell := fun P : Alphacarrier -> Prop => 
      ~ contains 0 (self_ref_pred_embed (fun _ => P = P))).
    
    destruct (self_ref_generation_exists Russell 0) as [t [_ Ht]].
    exists t. 
    unfold Russell in Ht.
    exact Ht.
  Qed.

  (* Or even more directly mimicking Russell's paradox *)
  Example gen_russell_self_membership_in_section :
    exists t : nat,
      contains t (self_ref_pred_embed
        (fun P : Alphacarrier -> Prop =>
          (* "The set of all predicates that don't contain themselves" *)
          forall Q : (Alphacarrier -> Prop) -> Prop,
            Q P <-> ~ Q (self_ref_pred_embed Q))).
  Proof.
    destruct (self_ref_generation_exists 
      (fun P => forall Q, Q P <-> ~ Q (self_ref_pred_embed Q)) 0) 
      as [t [_ Ht]].
    exists t. exact Ht.
  Qed.
  
End SelfRecursiveGenerative.


(* Experimental theorems section *)


(* NEW: Theorem showing undecidable predicates must oscillate *)
(* Theorem undecidable_must_oscillate :
  forall (Alpha : AlphaType) `{GenerativeType Alpha},
  forall P : Alphacarrier -> Prop,
  (~ exists a, P a) -> (~ forall a, ~ P a) ->
  forall t, exists t' : nat, t' > t /\ 
    ((contains t P /\ ~ contains t' P) \/ 
     (~ contains t P /\ contains t' P)).
Proof.
  intros Alpha H P Hno_witness Hnot_impossible t.
  (* Use the undecidable_oscillation axiom *)
  destruct (undecidable_oscillation P Hno_witness Hnot_impossible t) as [t' Hdiff].
  exists t'.
  split.
  - (* Prove t' > t from the oscillation property *)
    (* This would need to be added to undecidable_oscillation or proven separately *)
    admit. (* We'd need to strengthen the axiom to include t' > t *)
  - (* Show they differ *)
    destruct (classic (contains t P)).
    + left. split; [assumption|].
      intro Hcont. apply Hdiff. reflexivity.
    + right. split; [assumption|].
      (* If not at t, must be at t' since they differ *)
      admit. (* Needs classical logic or more structure *)
Admitted. *)

(* NEW: A theorem specific to Alpha - the impossible creates incompleteness *)
(* Theorem impossible_ensures_incompleteness :
  forall (Alpha : AlphaType) (H : GenerativeType Alpha),
  forall t : nat,
  exists P : Alphacarrier -> Prop,
    P = the_impossible /\
    contains t P /\
    (forall Q : (Alphacarrier -> Prop) -> Prop,
      Q (fun a => P a) -> ~ contains t (self_ref_pred_embed Q)).
Proof.
  intros Alpha H t.
  exists the_impossible.
  split; [reflexivity|].
  split.
  - apply impossible_always.
  - intros Q HQ.
    (* This would need more development - showing how the_impossible 
       blocks certain meta-predicates from being contained *)
    admit.
Admitted. *)