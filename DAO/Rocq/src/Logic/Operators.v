(** * Operators.v
    Symbolic operator calculus for DAO (ASCII-only, scoped notation)
    Usage:
      Require Import DAO.Logic.Operators.
      Open Scope dao_scope.
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.AlphaProperties.
Require Import DAO.Theory.Impossibility.ImpossibilityAlgebra.

Module DAOOperators.
  
  (* ================================================================ *)
  (** ** Core Operators *)
  (* ================================================================ *)
  
  (** Impossibility operator *)
  Definition Bot {Alpha : AlphaType} : Alphacarrier -> Prop := omega_veil.
  
  (** Truth operator *)
  Definition Top {Alpha : AlphaType} : Alphacarrier -> Prop := fun _ => True.
  
  (** Generalized conjunction *)
  Definition gen_and {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a /\ Q a.
  
  (** Generalized disjunction *)
  Definition gen_or {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a \/ Q a.
  
  (** Generalized implication *)
  Definition gen_implies {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a -> Q a.
  
  (** Negation via impossibility *)
  Definition gen_not {Alpha : AlphaType} (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a -> omega_veil a.
  
  (** Equivalence *)
  Definition gen_iff {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => P a <-> Q a.
  
  (** Impossibility test *)
  Definition is_impossible {Alpha : AlphaType} (P : Alphacarrier -> Prop) : Prop :=
    ImpossibilityAlgebra.Core.Is_Impossible P.
  
  (* ================================================================ *)
  (** ** Modal Operators *)
  (* ================================================================ *)
  
  (** Possibility: there exists a witness *)
  Definition Possible {Alpha : AlphaType} (P : Alphacarrier -> Prop) : Prop :=
    exists a, P a.
  
  (** Necessity: impossibility to not hold *)
  Definition Necessary {Alpha : AlphaType} (P : Alphacarrier -> Prop) : Prop :=
    forall a, P a \/ omega_veil a.
  
  (* ================================================================ *)
  (** ** Derived Combinators *)
  (* ================================================================ *)
  
  (** NAND *)
  Definition nand {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    gen_not (gen_and P Q).
  
  (** NOR *)
  Definition nor {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    gen_not (gen_or P Q).
  
  (** XOR *)
  Definition xor {Alpha : AlphaType} (P Q : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    gen_and (gen_or P Q) (gen_not (gen_and P Q)).
  
  (* ================================================================ *)
  (** ** Scoped Notations *)
  (* ================================================================ *)
  
  (** Create the DAO scope for notations *)
  Declare Scope dao_scope.
  Delimit Scope dao_scope with DAO.
  
  (** Bind the scope to Alphacarrier predicates *)
  Bind Scope dao_scope with Alphacarrier.
  
  (** Core logical operators *)
  Infix "AND" := gen_and (at level 40, left associativity) : dao_scope.
  Infix "OR" := gen_or (at level 50, left associativity) : dao_scope.
  Infix "==>" := gen_implies (at level 55, right associativity) : dao_scope.
  Notation "'NOT' P" := (gen_not P) (at level 35) : dao_scope.
  Infix "IFF" := gen_iff (at level 60) : dao_scope.
  
  (** Derived operators *)
  Infix "NAND" := nand (at level 40) : dao_scope.
  Infix "NOR" := nor (at level 50) : dao_scope.
  Infix "XOR" := xor (at level 50) : dao_scope.
  
  (** Constants and predicates *)
  Notation "'Bot'" := Bot : dao_scope.
  Notation "'Top'" := Top : dao_scope.
  Notation "'Impossible' P" := (is_impossible P) (at level 10) : dao_scope.
  Notation "'Possible' P" := (Possible P) (at level 30) : dao_scope.
  Notation "'Necessary' P" := (Necessary P) (at level 30) : dao_scope.
  
  (* ================================================================ *)
  (** ** Operator Laws (Algebraic Structure) *)
  (* ================================================================ *)
  
  Section OperatorLaws.
    Context {Alpha : AlphaType}.
    
    (* Open scope for this section *)
    Local Open Scope dao_scope.
    
    (** *** Conjunction laws *)
    
    Theorem and_commutative : forall P Q : Alphacarrier -> Prop,
      forall a, (P AND Q) a <-> (Q AND P) a.
    Proof.
      intros P Q a.
      unfold gen_and.
      split; intros [H1 H2]; split; assumption.
    Qed.
    
    Theorem and_associative : forall P Q R : Alphacarrier -> Prop,
      forall a, ((P AND Q) AND R) a <-> (P AND (Q AND R)) a.
    Proof.
      intros P Q R a.
      unfold gen_and.
      split.
      - intros [[HP HQ] HR]. split; [exact HP | split; [exact HQ | exact HR]].
      - intros [HP [HQ HR]]. split; [split; [exact HP | exact HQ] | exact HR].
    Qed.
    
    Theorem and_idempotent : forall P : Alphacarrier -> Prop,
      forall a, (P AND P) a <-> P a.
    Proof.
      intros P a.
      unfold gen_and.
      split; [intros [H _] | intro H; split]; assumption.
    Qed.
    
    Theorem and_top_identity : forall P : Alphacarrier -> Prop,
      forall a, (P AND Top) a <-> P a.
    Proof.
      intros P a.
      unfold gen_and, Top.
      split; [intros [H _] | intro H; split]; auto.
    Qed.
    
    Theorem and_bottom_absorb : forall P : Alphacarrier -> Prop,
      forall a, (P AND Bot) a <-> Bot a.
    Proof.
      intros P a.
      unfold gen_and, Bot, omega_veil.
      split.
      - intros [_ H]. exact H.
      - intro H. split; [exfalso; exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H) | exact H].
    Qed.
    
    (** *** Disjunction laws *)
    
    Theorem or_commutative : forall P Q : Alphacarrier -> Prop,
      forall a, (P OR Q) a <-> (Q OR P) a.
    Proof.
      intros P Q a.
      unfold gen_or.
      split; intros [H|H]; [right|left|right|left]; assumption.
    Qed.
    
    Theorem or_associative : forall P Q R : Alphacarrier -> Prop,
      forall a, ((P OR Q) OR R) a <-> (P OR (Q OR R)) a.
    Proof.
      intros P Q R a.
      unfold gen_or.
      split.
      - intros [[HP|HQ]|HR].
        + left. exact HP.
        + right. left. exact HQ.
        + right. right. exact HR.
      - intros [HP|[HQ|HR]].
        + left. left. exact HP.
        + left. right. exact HQ.
        + right. exact HR.
    Qed.
    
    Theorem or_idempotent : forall P : Alphacarrier -> Prop,
      forall a, (P OR P) a <-> P a.
    Proof.
      intros P a.
      unfold gen_or.
      split; [intros [H|H] | intro H; left]; assumption.
    Qed.
    
    Theorem or_bottom_identity : forall P : Alphacarrier -> Prop,
      forall a, (P OR Bot) a <-> P a.
    Proof.
      intros P a.
      unfold gen_or, Bot, omega_veil.
      split.
      - intros [H|H].
        + exact H.
        + exfalso. exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
      - intro H. left. exact H.
    Qed.
    
    Theorem or_top_absorb : forall P : Alphacarrier -> Prop,
      forall a, (P OR Top) a.
    Proof.
      intros P a.
      unfold gen_or, Top.
      right. exact I.
    Qed.
    
    (** *** Distribution laws *)
    
    Theorem and_distributes_over_or : forall P Q R : Alphacarrier -> Prop,
      forall a, (P AND (Q OR R)) a <-> ((P AND Q) OR (P AND R)) a.
    Proof.
      intros P Q R a.
      unfold gen_and, gen_or.
      split.
      - intros [HP [HQ|HR]].
        + left. split; assumption.
        + right. split; assumption.
      - intros [[HP HQ]|[HP HR]].
        + split. exact HP. left. exact HQ.
        + split. exact HP. right. exact HR.
    Qed.
    
    Theorem or_distributes_over_and : forall P Q R : Alphacarrier -> Prop,
      forall a, (P OR (Q AND R)) a <-> ((P OR Q) AND (P OR R)) a.
    Proof.
      intros P Q R a.
      unfold gen_and, gen_or.
      split.
      - intros [HP|[HQ HR]].
        + split; left; exact HP.
        + split; right; assumption.
      - intros [[HP|HQ] [HP'|HR]].
        + left. exact HP.
        + left. exact HP.
        + left. exact HP'.
        + right. split; assumption.
    Qed.
    
    (** *** Implication laws *)
    
    Theorem implies_reflexive : forall P : Alphacarrier -> Prop,
      forall a, (P ==> P) a.
    Proof.
      intros P a.
      unfold gen_implies.
      intro H. exact H.
    Qed.
    
    Theorem implies_transitive : forall P Q R : Alphacarrier -> Prop,
      forall a, ((P ==> Q) AND (Q ==> R)) a -> (P ==> R) a.
    Proof.
      intros P Q R a.
      unfold gen_and, gen_implies.
      intros [H1 H2] HP.
      apply H2. apply H1. exact HP.
    Qed.
    
    Theorem modus_ponens : forall P Q : Alphacarrier -> Prop,
      forall a, (P AND (P ==> Q)) a -> Q a.
    Proof.
      intros P Q a.
      unfold gen_and, gen_implies.
      intros [HP Himpl].
      apply Himpl. exact HP.
    Qed.
    
    (** *** Negation laws *)
    
    Theorem double_negation_intro : forall P : Alphacarrier -> Prop,
      forall a, P a -> (NOT (NOT P)) a.
    Proof.
      intros P a HP.
      unfold gen_not.
      intro HnP.
      apply HnP. exact HP.
    Qed.
    
    Theorem contradiction : forall P : Alphacarrier -> Prop,
      forall a, (P AND (NOT P)) a -> Bot a.
    Proof.
      intros P a.
      unfold gen_and, gen_not.
      intros [HP HnP].
      apply HnP. exact HP.
    Qed.
    
    Theorem explosion : forall P Q : Alphacarrier -> Prop,
      forall a, Bot a -> (P ==> Q) a.
    Proof.
      intros P Q a Hbot.
      unfold gen_implies.
      intro HP.
      exfalso.
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hbot).
    Qed.
    
    (** *** De Morgan's laws *)
    
    Theorem de_morgan_and : forall P Q : Alphacarrier -> Prop,
      forall a, (NOT (P AND Q)) a <-> ((NOT P) OR (NOT Q)) a.
    Proof.
      intros P Q a.
      unfold gen_not, gen_and, gen_or.
      split.
      - intro H.
        (* TODO: Need to use excluded middle or leave this for later *)
        (* We can derive classical logic fully constructively - we should look into a refactor for this *)
        (* We can potentially refactor classical logic construction more cleanly with our operators *)
        admit.
      - intros [HnP | HnQ] [HP HQ].
        + apply HnP. exact HP.
        + apply HnQ. exact HQ.
    Admitted.
    
    Theorem de_morgan_or : forall P Q : Alphacarrier -> Prop,
      forall a, (NOT (P OR Q)) a <-> ((NOT P) AND (NOT Q)) a.
    Proof.
      intros P Q a.
      unfold gen_not, gen_and, gen_or.
      split.
      - intro H. split; intro HP.
        + apply H. left. exact HP.
        + apply H. right. exact HP.
      - intros [HnP HnQ] [HP | HQ].
        + apply HnP. exact HP.
        + apply HnQ. exact HQ.
    Qed.

    (** Bridge between gen_not and standard negation *)
    Theorem gen_not_iff_not : forall (P : Alphacarrier -> Prop) (a : Alphacarrier),
      (NOT P) a <-> ~ (P a).
    Proof.
      intros P a.
      unfold gen_not.
      split.
      - (* gen_not -> ~ *)
        intros H HP.
        apply H in HP.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a HP).
      - (* ~ -> gen_not *)
        intros H HP.
        exfalso.
        apply H.
        exact HP.
    Qed.
    
  End OperatorLaws.
  
  (* ================================================================ *)
  (** ** Modal Operators *)
  (* ================================================================ *)
  
  Section ModalOperators.
    Context {Alpha : AlphaType}.
    
    Local Open Scope dao_scope.
    
    (** Modal axioms *)
    
    Theorem K_axiom : forall P Q : Alphacarrier -> Prop,
      Necessary (P ==> Q) -> Necessary P -> Necessary Q.
    Proof.
      intros P Q H1 H2 a.
      destruct (H1 a) as [Himpl | Hveil]; [|right; exact Hveil].
      destruct (H2 a) as [HP | Hveil]; [|right; exact Hveil].
      left.
      unfold gen_implies in Himpl.
      apply Himpl. exact HP.
    Qed.
    
    Theorem possibility_distributes : forall P Q : Alphacarrier -> Prop,
      Possible (P OR Q) <-> (Possible P) \/ (Possible Q).
    Proof.
      intros P Q.
      split.
      - intros [a [HP|HQ]].
        + left. exists a. exact HP.
        + right. exists a. exact HQ.
      - intros [[a HP]|[a HQ]]; exists a.
        + left. exact HP.
        + right. exact HQ.
    Qed.
    
    Theorem impossibility_characterization : forall P : Alphacarrier -> Prop,
      Impossible P <-> ~(Possible P).
    Proof.
      intro P.
      unfold is_impossible.
      split.
      - intros Himp [a HPa].
        destruct (Himp a) as [H _].
        apply H in HPa.
        exact (AlphaProperties.Core.omega_veil_has_no_witnesses a HPa).
      - intro Hnoposs.
        intro a.
        split.
        + intro HPa.
          exfalso.
          apply Hnoposs.
          exists a. exact HPa.
        + intro Hveil.
          exfalso.
          exact (AlphaProperties.Core.omega_veil_has_no_witnesses a Hveil).
    Qed.
    
    Theorem necessary_and : forall P Q : Alphacarrier -> Prop,
      Necessary P -> Necessary Q -> Necessary (P AND Q).
    Proof.
      intros P Q HP HQ a.
      destruct (HP a) as [HPa | Hveil]; [|right; exact Hveil].
      destruct (HQ a) as [HQa | Hveil]; [|right; exact Hveil].
      left.
      unfold gen_and. split; assumption.
    Qed.
    
    Theorem possible_or : forall P Q : Alphacarrier -> Prop,
      Possible P -> Possible (P OR Q).
    Proof.
      intros P Q [a HPa].
      exists a.
      unfold gen_or. left. exact HPa.
    Qed.
    
  End ModalOperators.
  
  (* ================================================================ *)
  (** ** Derived Combinator Properties *)
  (* ================================================================ *)
  
  Section DerivedCombinators.
    Context {Alpha : AlphaType}.
    
    Local Open Scope dao_scope.
    
    Theorem xor_symmetric : forall P Q : Alphacarrier -> Prop,
      forall a, (P XOR Q) a <-> (Q XOR P) a.
    Proof.
      intros P Q a.
      unfold xor, gen_and, gen_or, gen_not.
      tauto.
    Qed.
    
    Theorem xor_not_equal : forall P Q : Alphacarrier -> Prop,
      forall a, (P XOR Q) a -> ~((P AND Q) a).
    Proof.
      intros P Q a HXOR [HP HQ].
      unfold xor, gen_and, gen_not in HXOR.
      destruct HXOR as [_ H].
      specialize (H (conj HP HQ)).
      exact (AlphaProperties.Core.omega_veil_has_no_witnesses a H).
    Qed.
    
    Theorem nand_not_and : forall P Q : Alphacarrier -> Prop,
      forall a, (P NAND Q) a <-> (NOT (P AND Q)) a.
    Proof.
      intros P Q a.
      unfold nand. reflexivity.
    Qed.
    
  End DerivedCombinators.
  
  (* ================================================================ *)
  (** ** Convenient Tactics *)
  (* ================================================================ *)
  
  (** Tactic for applying operator laws *)
  Ltac op_rewrite :=
    repeat (rewrite and_commutative || 
            rewrite or_commutative || 
            rewrite and_associative || 
            rewrite or_associative ||
            rewrite and_idempotent ||
            rewrite or_idempotent).
  
  (** Tactic for simplifying with identity elements *)
  Ltac op_simplify :=
    repeat (rewrite and_top_identity || 
            rewrite or_bottom_identity ||
            rewrite and_bottom_absorb).
  
  (** Tactic for unfolding all operators *)
  Ltac unfold_ops :=
    unfold gen_and, gen_or, gen_implies, gen_not, gen_iff, Bot, Top.
  
End DAOOperators.

(** Export the module and open the scope by default *)
Export DAOOperators.

(** Users can disable by closing the scope:
    Close Scope dao_scope.
    
    Or use %DAO suffix:
    (P AND Q)%DAO
*)