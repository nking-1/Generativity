Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import Corelib.Classes.RelationClasses.

(* Scratchpad for theorems - stuff that hasn't been integrated elsewhere in the library *)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.

Section NaturalNumbersFromOmegaVeil.
  Context {Alpha : AlphaType}.
  
  (* ========== Foundation: Numbers as Negation Depth ========== *)
  
  (* Natural numbers are n negations of omega_veil *)
  Fixpoint NatN (n : nat) : Alphacarrier -> Prop :=
    match n with
    | 0 => omega_veil
    | S n' => fun a => ~ (NatN n' a)
    end.
  
  (* Zero is omega_veil - the impossible predicate *)
  Definition Zero : Alphacarrier -> Prop := NatN 0.
  
  (* Successor adds one negation *)
  Definition Succ (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    fun a => ~ P a.
  
  (* Basic properties *)
  Theorem zero_is_omega_veil :
    forall a, Zero a <-> omega_veil a.
  Proof.
    intro a. reflexivity.
  Qed.
  
  Theorem zero_has_no_witnesses :
    forall a, ~ Zero a.
  Proof.
    exact omega_veil_has_no_witnesses.
  Qed.
  
  Theorem one_has_witnesses :
    exists a, NatN 1 a.
  Proof.
    destruct alpha_not_empty as [a _].
    exists a.
    simpl. exact (omega_veil_has_no_witnesses a).
  Qed.
  
  (* Successor relation *)
  Theorem nat_succ :
    forall n, NatN (S n) = Succ (NatN n).
  Proof.
    intro n. reflexivity.
  Qed.
  
  (* ========== Addition as Composition ========== *)
  
  (* Addition in regular nat *)
  Fixpoint add_nat (m n : nat) : nat :=
    match m with
    | 0 => n
    | S m' => S (add_nat m' n)
    end.
  
  (* Key theorem: Adding m to n means applying m more negations *)
  Theorem addition_as_negation_composition :
    forall m n a,
    NatN (add_nat m n) a <-> 
    match m with
    | 0 => NatN n a
    | S m' => ~ NatN (add_nat m' n) a
    end.
  Proof.
    intros m n a.
    induction m.
    - (* m = 0 *)
      simpl. reflexivity.
    - (* m = S m' *)
      simpl. reflexivity.
  Qed.
  
  (* Cleaner statement: addition is iterated successor *)
  Fixpoint iterate_succ (m : nat) (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
    match m with
    | 0 => P
    | S m' => Succ (iterate_succ m' P)
    end.
  
  Theorem addition_is_iteration :
    forall m n,
    NatN (add_nat m n) = iterate_succ m (NatN n).
  Proof.
    intros m n.
    induction m.
    - reflexivity.
    - simpl. rewrite IHm. reflexivity.
  Qed.
  
  (* ========== Multiplication ========== *)
  
  (* Standard multiplication *)
  Fixpoint mult_nat (m n : nat) : nat :=
    match m with
    | 0 => 0
    | S m' => add_nat n (mult_nat m' n)
    end.
  
  (* Let's see what happens with small examples *)
  Example two_times_two :
    mult_nat 2 2 = 4.
  Proof. reflexivity. Qed.
  
  (* So NatN 4 = ~~~~omega_veil *)
  (* And NatN 2 = ~~omega_veil *)
  (* How do we get from ~~omega_veil to ~~~~omega_veil via multiplication? *)
  
  (* Insight: multiplication by m replaces each negation level with m levels *)
  (* But this is complex to express directly... *)
  
  (* For now, let's just verify that our multiplication gives the right type *)
  Theorem mult_gives_nat :
    forall m n,
    NatN (mult_nat m n) = NatN (mult_nat m n).
  Proof.
    reflexivity.
  Qed.
  
  (* ========== Key Properties ========== *)
  
  (* The parity of n determines if NatN n can have witnesses *)
  Theorem even_nat_no_witnesses :
    forall a, ~ NatN 0 a /\ ~ NatN 2 a /\ ~ NatN 4 a.
  Proof.
    intro a.
    split; [|split].
    - exact (omega_veil_has_no_witnesses a).
    - simpl. intro H. apply H. exact (omega_veil_has_no_witnesses a).
    - simpl. intro H. apply H. intro H'. apply H'. exact (omega_veil_has_no_witnesses a).
  Qed.
  
  (* This arithmetic is genuinely different from standard arithmetic! *)
  (* Even numbers are "impossible-like", odd numbers are "possible-like" *)
  
End NaturalNumbersFromOmegaVeil.


Require Import DAO.Core.AlphaType.
Require Import DAO.Core.AlphaProperties.
Require Import PeanoNat.

Section IntegersFromParity.
  Context {Alpha : AlphaType}.
  
  (* Define integers by splitting based on parity! *)
  Inductive IntZ : Type :=
    | Zneg : nat -> IntZ  (* negative integers use even indices: 0, 2, 4, ... *)
    | Zpos : nat -> IntZ  (* positive integers use odd indices: 1, 3, 5, ... *)
    .
  
  (* The key mapping: *)
  Definition IntZ_to_pred (z : IntZ) : Alphacarrier -> Prop :=
    match z with
    | Zneg n => NatN (2 * n)        (* -n maps to 2n (even) *)
    | Zpos n => NatN (2 * n + 1)    (* +n maps to 2n+1 (odd) *)
    end.
  
  (* Zero is special - it's Zneg 0 *)
  Definition Zero_int : IntZ := Zneg 0.
  
  Theorem zero_int_is_impossible :
    forall a, ~ (IntZ_to_pred Zero_int a).
  Proof.
    intro a. simpl.
    exact (omega_veil_has_no_witnesses a).
  Qed.
  
  (* Helper: all even NatN are impossible *)
  Lemma even_nat_impossible :
    forall k a, ~ NatN (2 * k) a.
  Proof.
    intros k a.
    induction k.
    - simpl. exact (omega_veil_has_no_witnesses a).
    - (* Need to show: ~ NatN (2 * S k) a *)
      (* First, let's simplify 2 * S k *)
      replace (2 * S k) with (S (S (2 * k))).
      2: { simpl. rewrite <- plus_n_O. rewrite <- plus_n_Sm. reflexivity. }
      
      (* Now NatN (S (S (2 * k))) = ~ ~ NatN (2 * k) *)
      simpl. 
      intro H.  (* H : ~ ~ NatN (2 * k) a *)
      apply H.
      intro H_2k. (* H_2k : NatN (2 * k) a *)
      (* But IHk says ~ NatN (2 * k) a *)
      exact (IHk H_2k).
  Qed.
  
  (* All negative numbers are "impossible-like" *)
  Theorem all_negatives_impossible :
    forall n a, ~ (IntZ_to_pred (Zneg n) a).
  Proof.
    intros n a.
    simpl. apply even_nat_impossible.
  Qed.
  
  (* Successor moves through: ..., -2, -1, 0, +1, +2, ... *)
  Definition succ_int (z : IntZ) : IntZ :=
    match z with
    | Zneg 0 => Zpos 0         (* 0 + 1 = +1 *)
    | Zneg (S n) => Zneg n     (* -(n+1) + 1 = -n *)
    | Zpos n => Zpos (S n)     (* +n + 1 = +(n+1) *)
    end.
  
  (* Predecessor *)
  Definition pred_int (z : IntZ) : IntZ :=
    match z with
    | Zneg n => Zneg (S n)     (* -n - 1 = -(n+1) *)
    | Zpos 0 => Zneg 0         (* +1 - 1 = 0 *)
    | Zpos (S n) => Zpos n     (* +(n+1) - 1 = +n *)
    end.
  
  (* Verify succ and pred are inverses *)
  Theorem succ_pred_inverse :
    forall z, pred_int (succ_int z) = z.
  Proof.
    intro z. destruct z; destruct n; reflexivity.
  Qed.
  
  Theorem pred_succ_inverse :
    forall z, succ_int (pred_int z) = z.
  Proof.
    intro z. destruct z; destruct n; reflexivity.
  Qed.
  
  (* Basic properties *)
  Example zero_succ_is_one :
    succ_int Zero_int = Zpos 0.
  Proof. reflexivity. Qed.
  
  Example neg_one_is_pred_zero :
    pred_int Zero_int = Zneg 1.
  Proof. reflexivity. Qed.
  
  (* The sign tells us about possibility! *)
  Definition is_possible_int (z : IntZ) : Prop :=
    exists a, IntZ_to_pred z a.
  
  Definition is_impossible_int (z : IntZ) : Prop :=
    forall a, ~ IntZ_to_pred z a.
  
  Theorem negative_impossible :
    forall n, is_impossible_int (Zneg n).
  Proof.
    intro n. unfold is_impossible_int.
    apply all_negatives_impossible.
  Qed.
  
  (* We could prove positive_possible with more work on odd NatN *)
  
End IntegersFromParity.


Section ConstructiveNegation.
  Context {Alpha : AlphaType}.
  
  (* If P is impossible (equals omega_veil), what about ~P? *)
  
  Theorem impossible_implies_negation_holds :
    forall P : Alphacarrier -> Prop,
    (forall a, P a <-> omega_veil a) ->
    forall a, ~ P a.
  Proof.
    intros P H a HPa.
    apply H in HPa.
    exact (omega_veil_has_no_witnesses a HPa).
  Qed.
  
  (* But can ~P also be impossible? Let's check: *)
  Theorem both_impossible_is_impossible :
    forall P : Alphacarrier -> Prop,
    (forall a, P a <-> omega_veil a) ->
    (forall a, ~ P a <-> omega_veil a) ->
    False.
  Proof.
    intros P HP HnP.
    destruct alpha_not_empty as [a _].
    
    (* From HP: P a <-> omega_veil a *)
    (* From HnP: ~P a <-> omega_veil a *)
    
    (* ~P a is true by the first theorem *)
    assert (~ P a).
    { intro HPa. apply HP in HPa. 
      exact (omega_veil_has_no_witnesses a HPa). }
    
    (* But HnP says ~P a <-> omega_veil a *)
    apply HnP in H.
    exact (omega_veil_has_no_witnesses a H).
  Qed.
  
  (* So if P is impossible, ~P CANNOT also be impossible *)
  
  (* But constructively, we have three options: *)
  Inductive Negation_Status (P : Alphacarrier -> Prop) : Type :=
    | P_Impossible : 
        (forall a, P a <-> omega_veil a) -> 
        Negation_Status P
    | NegP_Impossible : 
        (forall a, ~ P a <-> omega_veil a) -> 
        Negation_Status P  
    | Neither_Impossible :
        (exists a, ~ (P a <-> omega_veil a)) ->
        (exists a, ~ (~ P a <-> omega_veil a)) ->
        Negation_Status P.
  
  (* The key constructive insight: *)
  (* If P is impossible, then ~P is NOT impossible *)
  (* But we might not be able to prove ~P has witnesses! *)
  
  (* This is the constructive gap: *)
  (* P impossible → ~P holds *)
  (* But ~P holds ≠ ~P has witnesses *)
End ConstructiveNegation.

Section ImpossibilityNumbers.
  Context {Alpha : AlphaType}.
  
  (* First, let's verify that every natural number is realized *)
  Theorem every_nat_has_impossible_predicate :
    forall n : nat, exists P, Impossibility_Rank P n.
  Proof.
    induction n.
    - (* Base case: rank 0 *)
      exists omega_veil.
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

