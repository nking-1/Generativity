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
(* The Contradiction: Alpha Cannot Have Excluded Middle         *)
(* ============================================================ *)
Section AlphaNeedsThreeValues.
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
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
  Context {Omega : OmegaSet} {Alpha : AlphaSet}.
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

Section DynamicSystems.

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

(* Now let's connect System to AlphaSet conceptually *)
Section SystemAlphaConnection.
  Variable Alpha : AlphaSet.
  Variable sys : System.
  
  (* A System is like an AlphaSet evolving in time 
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

  (* Theorem no_perfect_tracking :
    ~(forall t : nat, exists t_o : nat,
      structure sys t = omega_structure omega t_o /\
      DS sys t = omega_DS omega t_o).
  Proof.
    intro H_track.
    
    (* Get sys's I_val bound *)
    destruct bounded_I_val as [I_bound H_bound].  (* Remove the 'sys' parameter *)
    
    (* Find where omega exceeds this bound *)
    destruct (omega_exceeds_any_bound (I_bound + 1)) as [t_big H_big].
    
    (* If sys perfectly tracks omega at t_big... *)
    destruct (H_track t_big) as [t_o [H_S H_DS]].
    
    (* Then sys would achieve I_val > I_bound *)
    pose proof (H_bound t_big) as H_sys_bound.
    
    (* But if sys matches omega's structure and DS at this time... *)
    unfold I_val in H_sys_bound.
    rewrite H_S, H_DS in H_sys_bound.
    unfold omega_I_val in H_big.
    
    (* We'd have sys's I_val = omega's I_val > I_bound *)
    (* This contradicts H_sys_bound *)
    lia.
  Qed. *)

End OmegaAlphaConnection.