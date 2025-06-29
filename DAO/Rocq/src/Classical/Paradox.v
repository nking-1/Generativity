Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.

(* This file proves paradox firewalls in the context of ClassicalAlphaType. *)

Section ParadoxFirewalls.
Context `{H_alpha: ClassicalAlphaType}.

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
    pred_equiv P classical_veil /\ (exists x, P x).
Proof.
  intros [P [Heq Hex]].
  destruct Hex as [x Px].
  apply (classical_veil_is_impossible x).
  apply Heq. exact Px.
Qed.

(* Every predicate is "grounded" - it can't circularly depend on its own truth value *)
Theorem predicate_grounding :
  forall (P : AlphaPred),
    (forall x, P x <-> exists y, P y) ->
    pred_equiv P classical_veil \/ pred_equiv P the_necessary.
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
    + intros _. exact (classical_veil_is_impossible z).
    + intros _. exact (H0 z).
Qed.

End ParadoxFirewalls.
