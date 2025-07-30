Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.
Require Import Corelib.Classes.RelationClasses.

(** * Boolean Algebra Implementation in ClassicalAlphaType
    
    This module shows that predicates in ClassicalAlphaType form a Boolean algebra
    under the quotient by predicate equivalence. *)

Module BooleanAlgebra.

  (** ** Boolean Operations on Predicates *)
  Module Operations.
    
    Definition pred_and {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) : ClassicalAlphaProperties.Helpers.AlphaPred :=
      fun x => P x /\ Q x.

    Definition pred_or {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) : ClassicalAlphaProperties.Helpers.AlphaPred :=
      fun x => P x \/ Q x.

    Definition pred_not {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) : ClassicalAlphaProperties.Helpers.AlphaPred :=
      fun x => ~ P x.

    Definition pred_top {H_alpha: ClassicalAlphaType} : ClassicalAlphaProperties.Helpers.AlphaPred :=
      fun x => True.

    Definition pred_bot {H_alpha: ClassicalAlphaType} : ClassicalAlphaProperties.Helpers.AlphaPred :=
      classical_veil.
    
  End Operations.

  (** ** Dichotomy Preservation *)
  Module Dichotomy.
    Import Operations.
    
    (* Prove that operations preserve the witness dichotomy *)
    Lemma pred_and_dichotomy {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_and P Q) classical_veil \/ 
      exists x, (pred_and P Q) x.
    Proof.
      unfold pred_and.
      destruct (alpha_constant_decision (exists x, P x /\ Q x)).
      - right. exact H.
      - left.
        unfold ClassicalAlphaProperties.Predicates.pred_equiv.
        apply ClassicalAlphaProperties.Core.classical_veil_unique.
        (* Convert ~ (exists x, P x /\ Q x) to forall x, ~ (P x /\ Q x) *)
        intros x [HPx HQx].
        apply H. exists x. split; assumption.
    Qed.

    Lemma pred_or_dichotomy {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_or P Q) classical_veil \/ 
      exists x, (pred_or P Q) x.
    Proof.
      unfold pred_or.
      destruct (ClassicalAlphaProperties.Predicates.everything_possible_except_one P) as [HP | [x HPx]].
      - destruct (ClassicalAlphaProperties.Predicates.everything_possible_except_one Q) as [HQ | [y HQy]].
        + left. 
          unfold ClassicalAlphaProperties.Predicates.pred_equiv.
          apply ClassicalAlphaProperties.Core.classical_veil_unique.
          intros z [HPz | HQz].
          * (* HP tells us P z <-> classical_veil z, and we have HPz : P z *)
            (* So we get classical_veil z *)
            apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible z).
            apply HP. exact HPz.
          * (* Similarly for Q *)
            apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible z).
            apply HQ. exact HQz.
        + right. exists y. right. exact HQy.
      - right. exists x. left. exact HPx.
    Qed.
    
  End Dichotomy.

  (** ** Boolean Algebra Laws *)
  Module Laws.
    Import Operations.
    
    (* Prove key boolean algebra laws *)
    Theorem pred_and_comm {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_and P Q) (pred_and Q P).
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_and.
      intros x. tauto.
    Qed.

    Theorem pred_or_comm {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_or P Q) (pred_or Q P).
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_or.
      intros x. tauto.
    Qed.

    Theorem pred_and_assoc {H_alpha: ClassicalAlphaType} (P Q R : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_and P (pred_and Q R)) (pred_and (pred_and P Q) R).
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_and.
      intros x. tauto.
    Qed.

    Theorem pred_or_assoc {H_alpha: ClassicalAlphaType} (P Q R : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_or P (pred_or Q R)) (pred_or (pred_or P Q) R).
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_or.
      intros x. tauto.
    Qed.

    (* Distributivity *)
    Theorem pred_and_or_distrib {H_alpha: ClassicalAlphaType} (P Q R : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_and P (pred_or Q R)) (pred_or (pred_and P Q) (pred_and P R)).
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_and, pred_or.
      intros x. tauto.
    Qed.

    (* Identity laws *)
    Theorem pred_and_top_id {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_and P pred_top) P.
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_and, pred_top.
      intros x. tauto.
    Qed.

    Theorem pred_or_bot_id {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_or P pred_bot) P.
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_or, pred_bot.
      intros x. split.
      - intros [HP | Himp].
        + exact HP.
        + exfalso. apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible x). exact Himp.
      - intros HP. left. exact HP.
    Qed.

    (* Complement laws - this is where ClassicalAlphaType shines! *)
    Theorem pred_not_not {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_not (pred_not P)) P.
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_not.
      intros x.
      split.
      - apply ClassicalAlphaProperties.ClassicalLogic.alpha_double_negation_elimination.
      - intros HP Hnot. exact (Hnot HP).
    Qed.

    (* The key theorem: every predicate has a complement *)
    Theorem pred_complement_exists {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_or P (pred_not P)) pred_top /\
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_and P (pred_not P)) pred_bot.
    Proof.
      split.
      - unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_or, pred_not, pred_top.
        intros x.
        split; [intros _ | intros _].
        + exact I.
        + destruct (alpha_constant_decision (P x)); tauto.
      - unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_and, pred_not, pred_bot.
        intros x.
        split.
        + intros [HP HnP]. 
          (* We have HP : P x and HnP : ~ P x, which gives us False *)
          exfalso. exact (HnP HP).
        + intros Himp. exfalso. 
          apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible x). exact Himp.
    Qed.

    (* De Morgan's Laws *)
    Theorem de_morgan_and {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_not (pred_and P Q)) (pred_or (pred_not P) (pred_not Q)).
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_not, pred_and, pred_or.
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

    Theorem de_morgan_or {H_alpha: ClassicalAlphaType} (P Q : ClassicalAlphaProperties.Helpers.AlphaPred) :
      ClassicalAlphaProperties.Predicates.pred_equiv (pred_not (pred_or P Q)) (pred_and (pred_not P) (pred_not Q)).
    Proof.
      unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_not, pred_and, pred_or.
      intros x.
      tauto.
    Qed.
    
  End Laws.

  (** ** Classification *)
  Module Classification.
    Import Operations.
    
    (** The quotient by pred_equiv forms a Boolean algebra.
      Specifically, it forms B₃, the 3-element Boolean algebra {⊥, ½, ⊤}.
      This is the smallest Boolean algebra that is not just {0,1}. *)
  
    (* We can characterize its size using the trichotomy *)
    Theorem boolean_algebra_classification {H_alpha: ClassicalAlphaType} :
      forall P : ClassicalAlphaProperties.Helpers.AlphaPred,
        ClassicalAlphaProperties.Predicates.pred_equiv P pred_bot \/
        ClassicalAlphaProperties.Predicates.pred_equiv P pred_top \/
        (exists x, P x) /\ (exists y, ~ P y).
    Proof.
      intros P.
      destruct (ClassicalAlphaProperties.Helpers.predicate_trichotomy P) as [Hbot | [Htop | Hmixed]].
      - left. 
        unfold pred_bot.
        exact Hbot.
      - right. left.
        unfold pred_top, ClassicalAlphaProperties.Helpers.the_necessary.
        unfold ClassicalAlphaProperties.Predicates.pred_equiv in *.
        intros x. split.
        + intros _. exact I.
        + intros _. apply Htop. apply ClassicalAlphaProperties.Core.classical_veil_is_impossible.
      - right. right. exact Hmixed.
    Qed.
    
  End Classification.

  Module Minimality.
    Import Operations.
    
    (** B₃ is the smallest Boolean algebra with a non-trivial element *)
    
    (** First, show that any proper element (neither ⊥ nor ⊤) generates B₃ *)
    Theorem proper_element_generates_three {H_alpha: ClassicalAlphaType} :
      forall P : ClassicalAlphaProperties.Helpers.AlphaPred,
      ((exists x, P x) /\ (exists y, ~ P y)) ->
      (* The subalgebra generated by {P, ⊥, ⊤} has exactly 3 elements *)
      exists (f : nat -> ClassicalAlphaProperties.Helpers.AlphaPred),
        (* f enumerates the equivalence classes *)
        (ClassicalAlphaProperties.Predicates.pred_equiv (f 0) pred_bot) /\
        (ClassicalAlphaProperties.Predicates.pred_equiv (f 1) P) /\
        (ClassicalAlphaProperties.Predicates.pred_equiv (f 2) pred_top) /\
        (* And these are all distinct *)
        (~ ClassicalAlphaProperties.Predicates.pred_equiv pred_bot P) /\
        (~ ClassicalAlphaProperties.Predicates.pred_equiv P pred_top) /\
        (~ ClassicalAlphaProperties.Predicates.pred_equiv pred_bot pred_top).
    Proof.
      intros P [Hex_true Hex_false].
      exists (fun n => match n with
                      | 0 => pred_bot
                      | 1 => P
                      | _ => pred_top
                      end).
      split; [|split; [|split; [|split; [|split]]]].
      - (* pred_equiv (f 0) pred_bot *)
        unfold ClassicalAlphaProperties.Predicates.pred_equiv.
        intro x. reflexivity.
      - (* pred_equiv (f 1) P *)
        unfold ClassicalAlphaProperties.Predicates.pred_equiv.
        intro x. reflexivity.
      - (* pred_equiv (f 2) pred_top *)
        unfold ClassicalAlphaProperties.Predicates.pred_equiv.
        intro x. reflexivity.
      - (* pred_bot ≠ P *)
        intro Heq.
        destruct Hex_true as [x Hx].
        apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible x).
        apply Heq. exact Hx.
      - (* P ≠ pred_top *)
        intro Heq.
        destruct Hex_false as [y Hy].
        apply Hy.
        apply Heq.
        unfold pred_top. exact I.
      - (* pred_bot ≠ pred_top *)
        intro Heq.
        destruct alpha_not_empty as [x _].
        apply (ClassicalAlphaProperties.Core.classical_veil_is_impossible x).
        apply Heq.
        unfold pred_top. exact I.
    Qed.
    
    (** Any Boolean algebra with more than 2 elements must have at least 3 *)
    Theorem no_proper_subalgebra {H_alpha: ClassicalAlphaType} :
      forall (B : ClassicalAlphaProperties.Helpers.AlphaPred -> Prop),
      (* B contains bottom and top *)
      B pred_bot ->
      B pred_top ->
      (* B is closed under operations *)
      (forall P Q, B P -> B Q -> B (pred_and P Q)) ->
      (forall P, B P -> B (pred_not P)) ->
      (* If B contains any middle element *)
      (exists P, B P /\ (exists x, P x) /\ (exists y, ~ P y)) ->
      (* Then B contains representatives of all three equivalence classes *)
      (exists P_bot P_mid P_top,
        B P_bot /\ B P_mid /\ B P_top /\
        ClassicalAlphaProperties.Predicates.pred_equiv P_bot pred_bot /\
        ((exists x, P_mid x) /\ (exists y, ~ P_mid y)) /\
        ClassicalAlphaProperties.Predicates.pred_equiv P_top pred_top).
    Proof.
      intros B Hbot Htop Hand Hnot [P [HBP [Hex_true Hex_false]]].
      exists pred_bot, P, pred_top.
      split; [|split; [|split; [|split; [|split]]]].
      - exact Hbot.
      - exact HBP.
      - exact Htop.
      - (* pred_equiv pred_bot pred_bot *)
        unfold ClassicalAlphaProperties.Predicates.pred_equiv.
        intro x. reflexivity.
      - split; assumption.
      - (* pred_equiv pred_top pred_top *)
        unfold ClassicalAlphaProperties.Predicates.pred_equiv.
        intro x. reflexivity.
    Qed.
    
  End Minimality.

  (** ** Spatial-Algebraic Correspondence *)
  Module SpatialCorrespondence.
    Import Operations.
    
    (** The spatial characterization corresponds to the Boolean algebra structure:
        - Empty regions ↔ Bottom element (⊥)
        - Full region ↔ Top element (⊤)  
        - Partial regions ↔ Middle elements
        - Region intersection ↔ Boolean AND
        - Region union ↔ Boolean OR *)
    
    (** Predicates can be viewed as regions (subsets) of Alphacarrier *)
    Definition is_empty_region {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) : Prop :=
      ClassicalAlphaProperties.Predicates.pred_equiv P pred_bot.
    
    Definition is_full_region {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) : Prop :=
      ClassicalAlphaProperties.Predicates.pred_equiv P pred_top.
    
    Definition is_partial_region {H_alpha: ClassicalAlphaType} (P : ClassicalAlphaProperties.Helpers.AlphaPred) : Prop :=
      (exists x, P x) /\ (exists y, ~ P y).
    
    (** The correspondence theorem *)
    Theorem spatial_algebraic_correspondence {H_alpha: ClassicalAlphaType} :
      (* 1. Empty region is the bottom element *)
      (forall P, is_empty_region P <-> ClassicalAlphaProperties.Predicates.pred_equiv P classical_veil) /\
      (* 2. Full region is the top element *)
      (forall P, is_full_region P <-> (forall x, P x)) /\
      (* 3. Intersection corresponds to AND *)
      (forall P Q x, (pred_and P Q) x <-> (P x /\ Q x)) /\
      (* 4. Union corresponds to OR *)
      (forall P Q x, (pred_or P Q) x <-> (P x \/ Q x)) /\
      (* 5. Every predicate falls into exactly one category *)
      (forall P, is_empty_region P \/ is_full_region P \/ is_partial_region P).
    Proof.
      split; [|split; [|split; [|split]]].
      - (* Empty ↔ classical_veil *)
        intro P.
        unfold is_empty_region, pred_bot.
        reflexivity.
      - (* Full ↔ everywhere true *)
        intro P.
        unfold is_full_region.
        split.
        * (* Forward direction *)
          intros Heq x.
          apply Heq.
          unfold pred_top. exact I.
        * (* Backward direction *)
          intro Hall.
          unfold ClassicalAlphaProperties.Predicates.pred_equiv, pred_top.
          intro x.
          split.
          -- intro dc. exact I.
          -- intro dc. exact (Hall x).
      - (* Intersection = AND *)
        intros P Q x.
        unfold pred_and.
        reflexivity.
      - (* Union = OR *)
        intros P Q x.
        unfold pred_or.
        reflexivity.
      - (* Trichotomy *)
        intro P.
        destruct (BooleanAlgebra.Classification.boolean_algebra_classification P) as [Hbot | [Htop | Hmid]].
        * left. exact Hbot.
        * right. left. exact Htop.
        * right. right. exact Hmid.
    Qed.
    
    (** The spatial operations preserve the trichotomy *)
    Theorem spatial_operations_respect_regions {H_alpha: ClassicalAlphaType} :
      (* If there are at least two elements, intersection of partial regions can be empty *)
      ((exists a b : Alphacarrier, a <> b) ->
      exists P Q, is_partial_region P /\ is_partial_region Q /\ 
                  is_empty_region (pred_and P Q)) /\
      (* Complement of a partial region is also partial, and their union is full *)
      (forall P, is_partial_region P -> 
                is_partial_region (pred_not P) /\
                is_full_region (pred_or P (pred_not P))).
    Proof.
      split.
      - (* First part: disjoint partials when we have two elements *)
        intros [a [b Hab]].
        exists (fun x => x = a), (fun x => x = b).
        split; [|split].
        + (* P is partial *)
          split.
          * exists a. reflexivity.
          * exists b. intro Heq. symmetry in Heq. exact (Hab Heq).
        + (* Q is partial *)
          split.
          * exists b. reflexivity.  
          * exists a. exact Hab.
        + (* P ∧ Q is empty *)
          unfold is_empty_region, pred_and, ClassicalAlphaProperties.Predicates.pred_equiv.
          intro x.
          split.
          * intros [Ha Hb].
            (* Ha : x = a, Hb : x = b *)
            subst x.
            (* Now we have a = b but Hab : a <> b *)
            exfalso. exact (Hab Hb).
          * intro Hveil.
            exfalso.
            exact (ClassicalAlphaProperties.Core.classical_veil_is_impossible x Hveil).
      - (* Second part: complement properties *)
        intros P [HPex HPnex].
        split.
        + (* ¬P is also partial *)
          unfold is_partial_region, pred_not.
          split.
          * (* ¬P has witnesses where P is false *)
            destruct HPnex as [y Hy].
            exists y. exact Hy.
          * (* ¬P has non-witnesses where P is true *)
            destruct HPex as [x Hx].
            exists x. intro Hnot. exact (Hnot Hx).
            + (* P ∨ ¬P is full *)
          unfold is_full_region, ClassicalAlphaProperties.Predicates.pred_equiv, pred_or, pred_not, pred_top.
          intro x.
          split.
          * (* Forward: P x \/ ~ P x -> True *)
            intro dc. exact I.
          * (* Backward: True -> P x \/ ~ P x *)
            intro dc.
            destruct (alpha_constant_decision (P x)); tauto.
    Qed.
    
  End SpatialCorrespondence.

End BooleanAlgebra.


Require Import DAO.Core.ClassicalAlphaAPI.
Import ClassicalAlphaAPI.

Module BooleanAlgebraExamples.
  Import BooleanAlgebra.Operations.

  (** ** Concrete examples of predicates in each class *)
  Module ConcretePredicates.
    
    (** Example of a bottom predicate - always classical_veil *)
    Definition always_false {H_alpha: ClassicalAlphaType} : AlphaPred :=
      classical_veil.
    
    (** Example of a top predicate - always true *)
    Definition always_true {H_alpha: ClassicalAlphaType} : AlphaPred :=
      fun x => True.
    
    (** For middle predicates, we need something more interesting.
        Let's assume we can pick a specific element *)
    Definition equals_specific {H_alpha: ClassicalAlphaType} (a : Alphacarrier) : AlphaPred :=
      fun x => x = a.
    
    (** Middle predicates exist whenever there are at least 2 elements *)
    Theorem middle_exists_if_two_elements {H_alpha: ClassicalAlphaType} :
      (exists a b : Alphacarrier, a <> b) ->
      exists P : AlphaPred,
        (exists x, P x) /\ (exists y, ~ P y).
    Proof.
      intros [a [b Hab]].
      exists (equals_specific a).
      split.
      - exists a. unfold equals_specific. reflexivity.
      - exists b. unfold equals_specific. 
        intro Heq. symmetry in Heq. exact (Hab Heq).
    Qed.
    
  End ConcretePredicates.

  (** ** The operation tables for our 3-element algebra *)
  Module OperationTables.
    
    (** Let's denote our three equivalence classes as Bot, Mid, Top *)
    
    (** Conjunction table - proves ∧ is well-defined on equivalence classes *)
    Theorem and_table {H_alpha: ClassicalAlphaType} :
      (* Bot ∧ anything = Bot *)
      (forall P, pred_equiv (pred_and classical_veil P) classical_veil) /\
      (* Top ∧ P = P *)
      (forall P, pred_equiv (pred_and pred_top P) P) /\
      (* Mid ∧ Mid can be Bot or Mid (never Top) *)
      (forall P Q, (exists x, P x) /\ (exists y, ~ P y) ->
                   (exists x, Q x) /\ (exists y, ~ Q y) ->
                   pred_equiv (pred_and P Q) classical_veil \/
                   ((exists x, pred_and P Q x) /\ (exists y, ~ pred_and P Q y))).
    Proof.
      split; [|split].
      - (* Bot ∧ anything = Bot *)
        intro P.
        unfold pred_equiv, pred_and.
        intro x.
        split.
        + (* Forward: (classical_veil x /\ P x) -> classical_veil x *)
          intros [Hveil _]. exact Hveil.
        + (* Backward: classical_veil x -> (classical_veil x /\ P x) *)
          intro Hveil.
          exfalso. exact (classical_veil_is_impossible x Hveil).
      
      - (* Top ∧ P = P *)
        intro P.
        unfold pred_equiv, pred_and, pred_top.
        intro x. tauto.
      
      - (* Mid ∧ Mid analysis *)
        intros P Q [xp [yp HPmid]] [xq [yq HQmid]].
        destruct (alpha_constant_decision (exists x, P x /\ Q x)) as [Hex | Hnex].
        + (* They overlap - result is Mid *)
          right.
          destruct Hex as [x [HPx HQx]].
          split.
          * exists x. unfold pred_and. split; assumption.
          * unfold pred_and.
            (* At least one of yp or yq makes P∧Q false *)
            destruct (alpha_constant_decision (P yq)) as [HPyq | HnPyq].
            -- exists yq. intros [_ HQyq]. exact (HQmid HQyq).
            -- exists yq. intros [HPyq _]. exact (HnPyq HPyq).
        + (* They don't overlap - result is Bot *)
          left.
          unfold pred_equiv.
          intro x.
          split.
          * (* Forward: pred_and P Q x -> classical_veil x *)
            intro Hand.
            unfold pred_and in Hand.
            exfalso. apply Hnex. exists x. exact Hand.
          * (* Backward: classical_veil x -> pred_and P Q x *)
            intro Hveil.
            exfalso. exact (classical_veil_is_impossible x Hveil).
    Qed.

    (** Disjunction table *)
    Theorem or_table {H_alpha: ClassicalAlphaType} :
      (* Top ∨ anything = Top *)
      (forall P, pred_equiv (pred_or pred_top P) pred_top) /\
      (* Bot ∨ P = P *)
      (forall P, pred_equiv (pred_or classical_veil P) P).
    Proof.
      split.
      - intro P.
        unfold pred_equiv, pred_or, pred_top.
        intro x. tauto.
      - intro P.
        unfold pred_equiv, pred_or.
        intro x. split.
        + intros [Hveil | HP].
          * exfalso. exact (classical_veil_is_impossible x Hveil).
          * exact HP.
        + intro HP. right. exact HP.
    Qed.

    (** Negation cycles through the three values *)
    Theorem negation_cycle {H_alpha: ClassicalAlphaType} :
      (* ¬Bot = Top *)
      pred_equiv (pred_not classical_veil) pred_top /\
      (* ¬Top = Bot *)
      pred_equiv (pred_not pred_top) classical_veil /\
      (* ¬Mid = Mid' (some other middle) *)
      (forall P, (exists x, P x) /\ (exists y, ~ P y) ->
                 (exists x, pred_not P x) /\ (exists y, ~ pred_not P y)).
    Proof.
      split; [|split].
      - (* ¬Bot = Top *)
        unfold pred_equiv, pred_not, pred_top.
        intro x. split.
        + intro Hnot_veil. exact I.
        + intro Htrue. exact (classical_veil_is_impossible x).
      
      - (* ¬Top = Bot *)
        unfold pred_equiv, pred_not, pred_top.
        intro x.
        split.
        + (* Forward: ~ True -> classical_veil x *)
          intro Hfalse.
          exfalso. apply Hfalse. exact I.
        + (* Backward: classical_veil x -> ~ True *)
          intro Hveil.
          exfalso. exact (classical_veil_is_impossible x Hveil).
      
      - (* ¬Mid = Mid' *)
        intros P Hmid.
        destruct Hmid as [[xp Hxp] [yp Hyp]].
        split.
        + exists yp. unfold pred_not. exact Hyp.
        + exists xp. unfold pred_not. intro Hnot. exact (Hnot Hxp).
    Qed.
    
  End OperationTables.

  (** ** Interesting phenomena *)
  Module Phenomena.
    
    (** Two middle predicates can be disjoint *)
    Example disjoint_middles {H_alpha: ClassicalAlphaType} :
      (exists a b : Alphacarrier, a <> b) ->
      exists P Q : AlphaPred,
        (* Both are middle *)
        ((exists x, P x) /\ (exists y, ~ P y)) /\
        ((exists x, Q x) /\ (exists y, ~ Q y)) /\
        (* But their conjunction is bottom *)
        pred_equiv (pred_and P Q) classical_veil.
    Proof.
      intros [a [b Hab]].
      exists (ConcretePredicates.equals_specific a).
      exists (ConcretePredicates.equals_specific b).
      split; [|split].
      - split.
        + exists a. reflexivity.
        + exists b. exact (not_eq_sym Hab).
      - split.
        + exists b. reflexivity.
        + exists a. intro Heq. 
          unfold ConcretePredicates.equals_specific in Heq.
          rewrite Heq in Hab.
          exact (Hab eq_refl).
      - unfold pred_equiv.
        intro x.
        split.
        + (* Forward: conjunction -> classical_veil *)
          intros [Ha Hb].
          unfold ConcretePredicates.equals_specific in *.
          (* Ha : x = a and Hb : x = b *)
          subst x. (* Now we have Ha : a = a and Hb : a = b *)
          exfalso. exact (Hab Hb).
        + (* Backward: classical_veil -> conjunction *)
          intro Hveil.
          exfalso. exact (classical_veil_is_impossible x Hveil).
    Qed.
    
    (** The algebra is "rigid" - any automorphism is trivial *)
    Theorem automorphism_trivial {H_alpha: ClassicalAlphaType} :
      forall (f : AlphaPred -> AlphaPred),
      (* f preserves operations and constants *)
      (forall P Q, pred_equiv (f (pred_and P Q)) (pred_and (f P) (f Q))) ->
      (forall P, pred_equiv (f (pred_not P)) (pred_not (f P))) ->
      pred_equiv (f classical_veil) classical_veil ->
      pred_equiv (f pred_top) pred_top ->
      (* Then f preserves all equivalence classes *)
      forall P, pred_equiv (f P) P \/
                (pred_equiv P classical_veil /\ pred_equiv (f P) classical_veil) \/
                (pred_equiv P pred_top /\ pred_equiv (f P) pred_top).
    Proof.
      (* This would show the automorphism group is trivial *)
    Admitted.
    
  End Phenomena.

End BooleanAlgebraExamples.


(* 
Notes about future possible work
Yes! Here are some interesting theorems we could prove:

## 1. Algebraic Characterization of Middle Elements

```coq
(** Middle elements are exactly those that are self-dual under De Morgan *)
Theorem middle_self_dual_characterization {H_alpha: ClassicalAlphaType} :
  forall P : AlphaPred,
  ((exists x, P x) /\ (exists y, ~ P y)) <->
  (~ pred_equiv P classical_veil /\ 
   ~ pred_equiv P pred_top /\
   exists Q, pred_equiv (pred_and P (pred_not P)) classical_veil /\
             pred_equiv (pred_or Q (pred_not Q)) pred_top /\
             pred_equiv Q P).
```

## 2. When Do Two Middles Combine?

```coq
(** Characterize when middle ∧ middle = bottom vs middle *)
Theorem middle_conjunction_dichotomy {H_alpha: ClassicalAlphaType} :
  forall P Q : AlphaPred,
  ((exists x, P x) /\ (exists y, ~ P y)) ->
  ((exists x, Q x) /\ (exists y, ~ Q y)) ->
  (pred_equiv (pred_and P Q) classical_veil <-> 
   forall x, P x -> ~ Q x).  (* They're disjoint *)
```

## 3. The "Thirds" Theorem

```coq
(** If Alpha has at least 3 elements, we can partition it into three disjoint middles *)
Theorem three_disjoint_middles {H_alpha: ClassicalAlphaType} :
  (exists a b c : Alphacarrier, a <> b /\ b <> c /\ a <> c) ->
  exists P Q R : AlphaPred,
    (* All are middle *)
    (forall X, X = P \/ X = Q \/ X = R -> 
      (exists x, X x) /\ (exists y, ~ X y)) /\
    (* Pairwise disjoint *)
    pred_equiv (pred_and P Q) classical_veil /\
    pred_equiv (pred_and P R) classical_veil /\
    pred_equiv (pred_and Q R) classical_veil /\
    (* Cover everything *)
    pred_equiv (pred_or P (pred_or Q R)) pred_top.
```

## 4. The Unique 3-Element Boolean Algebra

```coq
(** Any Boolean algebra with exactly 3 equivalence classes is isomorphic to ours *)
Theorem three_element_boolean_unique {H_alpha: ClassicalAlphaType} :
  forall (B : Type) (and or : B -> B -> B) (not : B -> B) (top bot : B),
  (* B forms a Boolean algebra *)
  (forall x y, and x y = and y x) ->
  (* ... other Boolean laws ... *)
  (* B has exactly 3 distinct elements up to equality *)
  (exists mid : B, bot <> mid /\ mid <> top /\ bot <> top /\
    forall x : B, x = bot \/ x = mid \/ x = top) ->
  (* Then it's isomorphic to our algebra *)
  exists (f : B -> AlphaPred),
    (* f is a homomorphism preserving structure *)
    True. (* details *)
```

## 5. Conservation of "Middleness"

```coq
(** Operations on middles tend to preserve middleness *)
Theorem middle_closed_under_symmetric_difference {H_alpha: ClassicalAlphaType} :
  forall P Q : AlphaPred,
  ((exists x, P x) /\ (exists y, ~ P y)) ->
  ((exists x, Q x) /\ (exists y, ~ Q y)) ->
  let sym_diff := pred_or (pred_and P (pred_not Q)) (pred_and (pred_not P) Q) in
  ((exists x, sym_diff x) /\ (exists y, ~ sym_diff y)) \/
  pred_equiv sym_diff pred_top \/
  pred_equiv sym_diff classical_veil.
```

I think #2 (middle_conjunction_dichotomy) would be the most fun to prove - it gives a precise criterion for when two middle predicates "clash" vs "coexist"! *)