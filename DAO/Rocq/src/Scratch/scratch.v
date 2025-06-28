(* Scratchpad for theorems - stuff that hasn't been integrated elsewhere in the library *)

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

