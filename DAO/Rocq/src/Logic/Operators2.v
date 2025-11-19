(** * Operators.v
    
    Three-valued modal operator calculus for DAO
    
    Three scopes:
    - dao_constructive_scope: Safe, ternary, intuitionistic (DEFAULT)
    - dao_classical_scope: Classical laws (requires alpha_classical)
    - dao_modal_scope: Modal operators (◇, □, etc.)
    
    Usage:
      Require Import DAO.Logic.Operators.
      Open Scope dao_constructive_scope.  (* Default *)
      (* or *)
      Open Scope dao_classical_scope.     (* Classical *)
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.

Module DAOOperators.
  
  (* ================================================================ *)
  (** ** Core Three-Valued Operators *)
  (* ================================================================ *)
  
  Section CoreOperators.
    Context {Alpha : AlphaType}.
    
    (** Impossibility (boundary value) *)
    Definition Bot : Alphacarrier -> Prop := omega_veil.
    
    (** Truth *)
    Definition Top : Alphacarrier -> Prop := fun _ => True.
    
    (** Three-valued conjunction *)
    Definition gen_and (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      fun a => P a /\ Q a.
    
    (** Three-valued disjunction *)
    Definition gen_or (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      fun a => P a \/ Q a.
    
    (** Three-valued implication *)
    Definition gen_implies (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      fun a => P a -> Q a.
    
    (** Three-valued negation (intuitionistic) *)
    Definition gen_not (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      fun a => P a -> Bot a.
    
    (** Equivalence *)
    Definition gen_iff (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      fun a => P a <-> Q a.
    
    (** Impossibility test *)
    Definition Is_Impossible (P : Alphacarrier -> Prop) : Prop :=
      ImpossibilityAlgebra.Core.Is_Impossible P.
    
  End CoreOperators.
  
  (* ================================================================ *)
  (** ** Modal Operators (Three-Valued) *)
  (* ================================================================ *)
  
  Section ModalOperators.
    Context {Alpha : AlphaType}.
    
    (** Possibility: there exists a witness outside boundary *)
    Definition Possible (P : Alphacarrier -> Prop) : Prop :=
      exists a, P a /\ ~ Bot a.
    
    (** Necessity: holds everywhere or is boundary *)
    Definition Necessary (P : Alphacarrier -> Prop) : Prop :=
      forall a, P a \/ Bot a.
    
    (** At boundary *)
    Definition AtBoundary (P : Alphacarrier -> Prop) : Prop :=
      forall a, P a -> Bot a.
    
    (** Contingent: possible but not necessary *)
    Definition Contingent (P : Alphacarrier -> Prop) : Prop :=
      Possible P /\ ~ Necessary P.
    
  End ModalOperators.
  
  (* ================================================================ *)
  (** ** Constructive Scope (Three-Valued Logic) *)
  (* ================================================================ *)
  
  Declare Scope dao_constructive_scope.
  Delimit Scope dao_constructive_scope with DAO_C.
  
  (** Core operators *)
  Infix "AND" := gen_and (at level 40, left associativity) : dao_constructive_scope.
  Infix "OR" := gen_or (at level 50, left associativity) : dao_constructive_scope.
  Infix "==>" := gen_implies (at level 55, right associativity) : dao_constructive_scope.
  Notation "'NOT' P" := (gen_not P) (at level 35) : dao_constructive_scope.
  Infix "IFF" := gen_iff (at level 60) : dao_constructive_scope.
  
  (** Constants *)
  Notation "'Bot'" := Bot : dao_constructive_scope.
  Notation "'Top'" := Top : dao_constructive_scope.
  
  (** Predicates *)
  Notation "'Impossible' P" := (Is_Impossible P) (at level 10) : dao_constructive_scope.
  Notation "'Possible' P" := (Possible P) (at level 10) : dao_constructive_scope.
  Notation "'Necessary' P" := (Necessary P) (at level 10) : dao_constructive_scope.
  
  (* ================================================================ *)
  (** ** Constructive Laws (Always Valid) *)
  (* ================================================================ *)
  
  Section ConstructiveLaws.
    Context {Alpha : AlphaType}.
    
    Local Open Scope dao_constructive_scope.
    
    (** *** Conjunction *)
    
    Theorem and_commutative : forall P Q : Alphacarrier -> Prop,
      forall a, (P AND Q) a <-> (Q AND P) a.
    Proof.
      intros P Q a. unfold gen_and. tauto.
    Qed.
    
    Theorem and_associative : forall P Q R : Alphacarrier -> Prop,
      forall a, ((P AND Q) AND R) a <-> (P AND (Q AND R)) a.
    Proof.
      intros P Q R a. unfold gen_and. tauto.
    Qed.
    
    Theorem and_idempotent : forall P : Alphacarrier -> Prop,
      forall a, (P AND P) a <-> P a.
    Proof.
      intros P a. unfold gen_and. tauto.
    Qed.
    
    Theorem and_top_identity : forall P : Alphacarrier -> Prop,
      forall a, (P AND Top) a <-> P a.
    Proof.
      intros P a. unfold gen_and, Top. tauto.
    Qed.
    
    Theorem and_bottom_absorb : forall P : Alphacarrier -> Prop,
      forall a, (P AND Bot) a <-> Bot a.
    Proof.
      intros P a. unfold gen_and, Bot.
      split; [intros [_ H] | intro H]; 
        [exact H | split; 
          [exfalso; exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H) | exact H]].
    Qed.
    
    (** *** Disjunction *)
    
    Theorem or_commutative : forall P Q : Alphacarrier -> Prop,
      forall a, (P OR Q) a <-> (Q OR P) a.
    Proof.
      intros P Q a. unfold gen_or. tauto.
    Qed.
    
    Theorem or_associative : forall P Q R : Alphacarrier -> Prop,
      forall a, ((P OR Q) OR R) a <-> (P OR (Q OR R)) a.
    Proof.
      intros P Q a. unfold gen_or. tauto.
    Qed.
    
    Theorem or_idempotent : forall P : Alphacarrier -> Prop,
      forall a, (P OR P) a <-> P a.
    Proof.
      intros P a. unfold gen_or. tauto.
    Qed.
    
    Theorem or_bottom_identity : forall P : Alphacarrier -> Prop,
      forall a, (P OR Bot) a <-> P a.
    Proof.
      intros P a. unfold gen_or, Bot.
      split; [intros [H|H] | intro H; left]; 
        [exact H | exfalso; exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H) | exact H].
    Qed.
    
    Theorem or_top_absorb : forall P : Alphacarrier -> Prop,
      forall a, (P OR Top) a.
    Proof.
      intros P a. unfold gen_or, Top. right. exact I.
    Qed.
    
    (** *** Distribution *)
    
    Theorem and_distributes_over_or : forall P Q R : Alphacarrier -> Prop,
      forall a, (P AND (Q OR R)) a <-> ((P AND Q) OR (P AND R)) a.
    Proof.
      intros P Q R a. unfold gen_and, gen_or. tauto.
    Qed.
    
    Theorem or_distributes_over_and : forall P Q R : Alphacarrier -> Prop,
      forall a, (P OR (Q AND R)) a <-> ((P OR Q) AND (P OR R)) a.
    Proof.
      intros P Q R a. unfold gen_and, gen_or. tauto.
    Qed.
    
    (** *** Implication *)
    
    Theorem implies_reflexive : forall P : Alphacarrier -> Prop,
      forall a, (P ==> P) a.
    Proof.
      intros P a. unfold gen_implies. auto.
    Qed.
    
    Theorem implies_transitive : forall P Q R : Alphacarrier -> Prop,
      forall a, ((P ==> Q) AND (Q ==> R)) a -> (P ==> R) a.
    Proof.
      intros P Q R a. unfold gen_and, gen_implies. tauto.
    Qed.
    
    Theorem modus_ponens : forall P Q : Alphacarrier -> Prop,
      forall a, (P AND (P ==> Q)) a -> Q a.
    Proof.
      intros P Q a. unfold gen_and, gen_implies. tauto.
    Qed.
    
    (** *** Negation (Intuitionistic) *)
    
    Theorem double_negation_intro : forall P : Alphacarrier -> Prop,
      forall a, P a -> (NOT (NOT P)) a.
    Proof.
      intros P a HP. unfold gen_not. intro H. apply H. exact HP.
    Qed.
    
    Theorem contradiction : forall P : Alphacarrier -> Prop,
      forall a, (P AND (NOT P)) a -> Bot a.
    Proof.
      intros P a. unfold gen_and, gen_not. intros [HP HnP]. apply HnP. exact HP.
    Qed.
    
    Theorem explosion : forall P Q : Alphacarrier -> Prop,
      forall a, Bot a -> (P ==> Q) a.
    Proof.
      intros P Q a Hbot. unfold gen_implies.
      intro. exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hbot).
    Qed.
    
    (** *** De Morgan (Constructive Direction Only) *)
    
    Theorem de_morgan_or : forall P Q : Alphacarrier -> Prop,
      forall a, (NOT (P OR Q)) a <-> ((NOT P) AND (NOT Q)) a.
    Proof.
      intros P Q a. unfold gen_not, gen_and, gen_or.
      split; [intro H; split; intro HP; apply H | intros [HnP HnQ] [HP|HQ]];
        [left; exact HP | right; exact HP | apply HnP; exact HP | apply HnQ; exact HQ].
    Qed.
    
    (** Reverse direction needs classicality *)
    Theorem de_morgan_and_one_direction : forall P Q : Alphacarrier -> Prop,
      forall a, ((NOT P) OR (NOT Q)) a -> (NOT (P AND Q)) a.
    Proof.
      intros P Q a. unfold gen_or, gen_not, gen_and.
      intros [HnP|HnQ] [HP HQ]; [apply HnP | apply HnQ]; assumption.
    Qed.
    
    (** *** Three-Valued Trichotomy *)
    
    (** In three-valued logic, we have trichotomy *)
    Theorem ternary_trichotomy : forall P : Alphacarrier -> Prop,
      (Possible P) \/ (Possible (NOT P)) \/ (AtBoundary P).
    Proof.
      intro P.
      (* This actually requires some axiom about Alpha having at least one non-boundary point *)
      (* Or we accept that everything might be at boundary *)
      (* For now, we state it as an axiom *)
    Admitted. (* TODO: Derive from AlphaType richness *)
    
  End ConstructiveLaws.
  
  (* ================================================================ *)
  (** ** Classical Scope (Requires Excluded Middle) *)
  (* ================================================================ *)
  
  Declare Scope dao_classical_scope.
  Delimit Scope dao_classical_scope with DAO_CL.
  
  (** Inherit all constructive notations *)
  Infix "AND" := gen_and (at level 40, left associativity) : dao_classical_scope.
  Infix "OR" := gen_or (at level 50, left associativity) : dao_classical_scope.
  Infix "==>" := gen_implies (at level 55, right associativity) : dao_classical_scope.
  Notation "'NOT' P" := (gen_not P) (at level 35) : dao_classical_scope.
  Infix "IFF" := gen_iff (at level 60) : dao_classical_scope.
  Notation "'Bot'" := Bot : dao_classical_scope.
  Notation "'Top'" := Top : dao_classical_scope.
  
  Section ClassicalLaws.
    Context {Alpha : AlphaType}.
    
    (** Classical assumption: excluded middle *)
    Hypothesis alpha_classical : forall P : Alphacarrier -> Prop,
      forall a, P a \/ ~ P a.
    
    Local Open Scope dao_classical_scope.
    
    (** *** Classical-only theorems *)
    
    (** Double negation elimination *)
    Theorem double_negation_elim : forall P : Alphacarrier -> Prop,
      forall a, (NOT (NOT P)) a -> P a.
    Proof.
      intros P a HnnP. unfold gen_not in HnnP.
      destruct (alpha_classical P a) as [HP|HnP]; [exact HP | exfalso; apply HnnP; exact HnP].
    Qed.
    
    (** Excluded middle *)
    Theorem excluded_middle : forall P : Alphacarrier -> Prop,
      forall a, (P OR (NOT P)) a.
    Proof.
      intros P a. unfold gen_or, gen_not.
      destruct (alpha_classical P a) as [HP|HnP]; [left | right]; assumption.
    Qed.
    
    (** De Morgan (reverse direction) *)
    Theorem de_morgan_and : forall P Q : Alphacarrier -> Prop,
      forall a, (NOT (P AND Q)) a <-> ((NOT P) OR (NOT Q)) a.
    Proof.
      intros P Q a. unfold gen_not, gen_and, gen_or.
      split.
      - intro H.
        destruct (alpha_classical P a) as [HP|HnP]; [right | left; exact HnP].
        intro HQ. apply H. split; assumption.
      - intros [HnP|HnQ] [HP HQ]; [apply HnP | apply HnQ]; assumption.
    Qed.
    
    (** Classical laws follow from excluded middle as ONE-LINERS *)
    
    (** Contrapositive *)
    Theorem contrapositive : forall P Q : Alphacarrier -> Prop,
      forall a, (P ==> Q) a -> ((NOT Q) ==> (NOT P)) a.
    Proof.
      intros; unfold gen_implies, gen_not in *; auto.
    Qed.
    
    Theorem contrapositive_iff : forall P Q : Alphacarrier -> Prop,
      forall a, (P ==> Q) a <-> ((NOT Q) ==> (NOT P)) a.
    Proof.
      intros; split; apply contrapositive || (unfold gen_implies, gen_not; 
        destruct (alpha_classical P a); destruct (alpha_classical Q a); auto).
    Qed.
    
    (** Pierce's law *)
    Theorem pierce : forall P Q : Alphacarrier -> Prop,
      forall a, (((P ==> Q) ==> P) ==> P) a.
    Proof.
      intros; unfold gen_implies; destruct (alpha_classical P a); auto.
    Qed.
    
    (** Material implication *)
    Theorem material_implication : forall P Q : Alphacarrier -> Prop,
      forall a, (P ==> Q) a <-> ((NOT P) OR Q) a.
    Proof.
      intros; unfold gen_implies, gen_not, gen_or; 
        destruct (alpha_classical P a); tauto.
    Qed.
    
    (** Reductio ad absurdum *)
    Theorem reductio_ad_absurdum : forall P : Alphacarrier -> Prop,
      forall a, ((NOT P) ==> Bot) a -> P a.
    Proof.
      intros; unfold gen_implies, gen_not in *;
        destruct (alpha_classical P a); auto.
    Qed.
    
  End ClassicalLaws.
  
  (* ================================================================ *)
  (** ** Modal Scope *)
  (* ================================================================ *)
  
  Declare Scope dao_modal_scope.
  Delimit Scope dao_modal_scope with DAO_M.
  
  (** Modal notations *)
  Notation "'◇' P" := (Possible P) (at level 30) : dao_modal_scope.
  Notation "'□' P" := (Necessary P) (at level 30) : dao_modal_scope.
  Notation "'@' P" := (AtBoundary P) (at level 30) : dao_modal_scope.
  
  Section ModalLaws.
    Context {Alpha : AlphaType}.
    
    Local Open Scope dao_modal_scope.
    Local Open Scope dao_constructive_scope.
    
    (** Modal axioms (K, T, etc.) *)
    
    Theorem modal_K : forall P Q : Alphacarrier -> Prop,
      □ (P ==> Q) -> □ P -> □ Q.
    Proof.
      intros P Q H1 H2 a.
      destruct (H1 a) as [Himpl|Hveil]; [|right; exact Hveil].
      destruct (H2 a) as [HP|Hveil]; [|right; exact Hveil].
      left. unfold gen_implies in Himpl. apply Himpl. exact HP.
    Qed.
    
    Theorem modal_T : forall P : Alphacarrier -> Prop,
      □ P -> ◇ P.
    Proof.
      intros P Hnec.
      (* Need at least one non-boundary point *)
    Admitted. (* Requires AlphaType richness *)
    
    Theorem modal_duality : forall P : Alphacarrier -> Prop,
      ~ (◇ P) <-> (@ P).
    Proof.
      intro P. unfold Possible, AtBoundary, Bot. split.
      - intros Hnoposs a HPa.
        destruct (alpha_classical omega_veil a) as [|Hnveil].
        + assumption.
        + exfalso. apply Hnoposs. exists a. split; assumption.
      - intros Hbound [a [HPa Hnveil]].
        apply Hnveil. apply Hbound. exact HPa.
    Qed.
    
    Theorem possibility_distributes : forall P Q : Alphacarrier -> Prop,
      ◇ (P OR Q) <-> (◇ P) \/ (◇ Q).
    Proof.
      intros P Q. split.
      - intros [a [[HP|HQ] Hnveil]]; [left | right]; exists a; split; assumption.
      - intros [[a [HP Hnveil]]|[a [HQ Hnveil]]]; exists a; split; 
          [left | | right |]; assumption.
    Qed.
    
    Theorem necessity_distributes : forall P Q : Alphacarrier -> Prop,
      □ (P AND Q) <-> (□ P) /\ (□ Q).
    Proof.
      intros P Q. unfold Necessary, gen_and. split.
      - intro H. split; intro a; destruct (H a) as [[HP HQ]|Hveil]; 
          [left; assumption | left; assumption | right; assumption | right; assumption].
      - intros [HP HQ] a. 
        destruct (HP a) as [HPa|Hveil]; [|right; exact Hveil].
        destruct (HQ a) as [HQa|Hveil]; [|right; exact Hveil].
        left. split; assumption.
    Qed.
    
  End ModalLaws.
  
  (* ================================================================ *)
  (** ** Convenient Tactics *)
  (* ================================================================ *)
  
  Ltac unfold_ops :=
    unfold gen_and, gen_or, gen_implies, gen_not, gen_iff, Bot, Top.
  
  Ltac dao_simplify :=
    repeat (rewrite ?and_commutative, ?or_commutative,
            ?and_associative, ?or_associative,
            ?and_idempotent, ?or_idempotent,
            ?and_top_identity, ?or_bottom_identity).
  
  Ltac dao_trivial :=
    unfold_ops; intuition;
    try (exfalso; apply AlphaProperties.Core.omega_veil_has_no_witnesses; assumption).
  
  Ltac dao_classical :=
    match goal with
    | |- context[gen_not (gen_not ?P)] => 
        apply double_negation_elim
    | |- context[gen_or ?P (gen_not ?P)] =>
        apply excluded_middle
    | |- (gen_implies ?P ?Q) _ <-> (gen_or (gen_not ?P) ?Q) _ =>
        apply material_implication
    end.
  
End DAOOperators.

Export DAOOperators.

(** Default scope: constructive (safe) *)
Open Scope dao_constructive_scope.