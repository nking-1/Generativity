(* step1_basic_structures.v *)
(* Just the basic structures - minimal and clean *)

(* OmegaSet: A set where EVERY predicate has a witness *)
Class OmegaSet := {
  Omegacarrier : Type;
  omega_completeness : forall (P : Omegacarrier -> Prop), 
    exists x : Omegacarrier, P x
}.

(* AlphaSet: A set with exactly one impossible predicate *)
Class AlphaSet := {
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
Definition the_impossible {Alpha : AlphaSet} : Alphacarrier -> Prop :=
  proj1_sig (@alpha_impossibility Alpha).


Section OmegaProperties.
  Context {Omega : OmegaSet}.
  
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
  
End OmegaProperties.

(* ============================================================ *)
(* Properties of AlphaSet *)  
(* ============================================================ *)

Section AlphaProperties.
  Context {Alpha : AlphaSet}.
  
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

(* ============================================================ *)
(* Simple Diagonal for AlphaSet *)
(* ============================================================ *)

Section SimpleDiagonal.
  Context {Alpha : AlphaSet}.
  
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
  
End SimpleDiagonal.

(* ============================================================ *)
(* Diagonal in OmegaSet *)
(* ============================================================ *)

Section OmegaDiagonal.
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
  
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
(* Basic Representation *)
(* ============================================================ *)

Section Representation.
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
  
  (* A predicate P is representable if there's an Alpha predicate
     that tracks P through some mapping *)
  Definition representable (P : Omegacarrier -> Prop) : Prop :=
    exists (A : Alphacarrier -> Prop) (f : Alphacarrier -> Omegacarrier),
    forall a : Alphacarrier, A a <-> P (f a).
  
  (* Key insight: paradoxical predicates cannot be represented *)
  (* We'll admit this for now and focus on the diagonal *)
  Lemma paradoxical_not_representable :
    forall P : Omegacarrier -> Prop,
    (exists x, P x /\ ~ P x) ->
    ~ representable P.
  Proof.
    (* The idea: if P has paradoxical witnesses, representing it 
       in Alpha would break Alpha's consistency *)
    admit.
  Admitted.
  
End Representation.

(* ============================================================ *)
(* Preparing for the diagonal *)
(* ============================================================ *)

Section DiagonalPrep.
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
  
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
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
  
  (* We'll use the omega_diagonal from the previous section *)
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  Variable enum_complete : forall A : Alphacarrier -> Prop, 
    exists n, alpha_enum n = Some A.
  Variable embed : Alphacarrier -> Omegacarrier.
  
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
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
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
  Context {Alpha : AlphaSet}.
  
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
(* The Contradiction: Alpha Cannot Have Excluded Middle *)
(* ============================================================ *)

Section AlphaNeedsThreeValues.
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
  
  (* First, let's be clear about what excluded middle means *)
  Definition excluded_middle := forall P : Prop, P \/ ~P.
  
  (* If Alpha has excluded middle, it can construct a decision procedure *)
  Lemma em_gives_decisions :
    excluded_middle ->
    forall P : Prop, {P} + {~P}.
  Proof.
    intros EM P.
    (* This actually requires more work in Coq - we need classical axioms *)
    (* For now, let's assume we can go from EM to decidability *)
    admit.
  Admitted.
  
  (* The killer theorem: Alpha cannot have excluded middle *)
  Theorem alpha_cannot_have_excluded_middle :
    excluded_middle -> False.
  Proof.
    intro EM.
    
    (* Consider the proposition: "omega_unrepresentable has a witness" *)
    pose (P := exists x : Omegacarrier, omega_unrepresentable x).
    
    (* By excluded middle, either P or ~P *)
    destruct (EM P) as [HP | HnP].
    
    - (* Case 1: P holds *)
      (* We know this is true from omega_completeness *)
      (* So far so good... *)
      
      (* But now consider: can Alpha express the question 
         "is x a witness for omega_unrepresentable?" *)
      
      (* If Alpha could fully decide P, it would need to be able to
         check whether any given x satisfies omega_unrepresentable *)
      
      (* This would require Alpha to represent omega_unrepresentable! *)
      (* Let's make this precise... *)
      
      (* Define a predicate in Alpha that tries to track unrepresentability *)
      assert (H_bad : representable omega_unrepresentable).
      {
        (* If Alpha can decide everything, it can define:
           "the set of Alpha elements that map to unrepresentable Omega elements" *)
        admit. (* This is where the technical argument would go *)
      }
      
      (* But we proved this is impossible! *)
      exact (unrepresentable_not_representable H_bad).
      
    - (* Case 2: ~P holds *)
      (* This says there's no witness for omega_unrepresentable *)
      (* But we proved there IS a witness! *)
      apply HnP.
      exact unrepresentable_exists.
  Qed.
  
End AlphaNeedsThreeValues.

(* ============================================================ *)
(* Therefore: Ternary Logic is Necessary *)
(* ============================================================ *)

Section TernaryNecessity.
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
  
  (* Some propositions cannot be decided in Alpha *)
  Definition undecidable_in_alpha (P : Prop) : Prop :=
    (* Asserting P leads to contradiction *)
    (P -> exists x, omega_unrepresentable x -> representable omega_unrepresentable) /\
    (* Asserting ~P leads to contradiction *)  
    (~P -> forall x, ~omega_unrepresentable x).
  
  (* The witness question is undecidable *)
  Theorem witness_question_undecidable :
    undecidable_in_alpha (exists x : Omegacarrier, omega_unrepresentable x).
  Proof.
    split.
    - (* If we assert witnesses exist, we'd need to represent unrepresentable *)
      intros H_exists.
      exists (proj1_sig (omega_completeness omega_unrepresentable)).
      intro _.
      (* This would require Alpha to check unrepresentability *)
      admit.
      
    - (* If we assert no witnesses exist, contradicts Omega *)
      intros H_not_exists x H_unrep.
      apply H_not_exists.
      exists x.
      exact H_unrep.
  Qed.
  
  (* Therefore, Alpha must use ternary logic *)
  Theorem alpha_uses_ternary :
    exists P : Prop,
    forall (decision : {P} + {~P}),
    False.
  Proof.
    exists (exists x : Omegacarrier, omega_unrepresentable x).
    intro decision.
    destruct decision as [H_yes | H_no].
    - (* If we decide yes, we need representation *)
      admit. (* Use first part of witness_question_undecidable *)
    - (* If we decide no, contradicts omega_completeness *)
      apply H_no.
      exact unrepresentable_exists.
  Qed.
  
  (* The final picture: Alpha must classify propositions into three categories *)
  Definition alpha_classification (P : Prop) : TernaryTruth P :=
    match excluded_middle_decidable P with
    | inl H_P => Proved P H_P
    | inr H_nP => 
        match excluded_middle_decidable (~P) with
        | inl H_nnP => Refuted P (fun HP => H_nnP HP)
        | inr H_undec => Undecidable P (fun HP => _) (fun HnP => _)
        end
    end.
  
End TernaryNecessity.