Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.

(* ============================================================ *)
(* Simple Diagonal for AlphaType *)
(* ============================================================ *)

Section AlphaSelfDiagonal.
  Context {Alpha : AlphaType}.
  
  (* Assume we can enumerate Alpha's predicates *)
  Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
  
  (* The diagonal: flips the nth predicate at position n *)
  Definition alpha_diagonal_pred : nat -> Alphacarrier -> Prop :=
    fun n => match alpha_enum n with
    | Some P => fun a => ~ P a
    | None => fun _ => True
    end.
  
  (* For any enumerated predicate, the diagonal differs from it *)
  Theorem alpha_diagonal_differs :
    forall n P a,
    alpha_enum n = Some P ->
    ~ (P a <-> alpha_diagonal_pred n a).
  Proof.
    intros n P a Henum H_iff.
    unfold alpha_diagonal_pred in H_iff.
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
      alpha_diagonal_pred alpha_enum n a.
  
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
    embed a = x /\ alpha_diagonal_pred alpha_enum n a.
  Proof.
    intro n.
    pose (pred_n := fun x => exists a, embed a = x /\ alpha_diagonal_pred alpha_enum n a).
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
    alpha_enum n <> Some (fun a => alpha_diagonal_pred alpha_enum n a).
  Proof.
    intros n Heq.
    (* Extract the predicate from the enumeration *)
    assert (H_contra : forall a, 
      alpha_diagonal_pred alpha_enum n a <-> alpha_diagonal_pred alpha_enum n a).
    { intro a. split; auto. }
    
    (* But by diagonal_differs, if alpha_enum n = Some P, then
      P cannot equal alpha_diagonal_pred alpha_enum n *)
    pose (P := fun a => alpha_diagonal_pred alpha_enum n a).
    destruct alpha_not_empty as [a0 _].
    
    (* From Heq, we have alpha_enum n = Some P *)
    (* By alpha_diagonal_differs, we should have ~ (P a0 <-> alpha_diagonal_pred alpha_enum n a0) *)
    apply (alpha_diagonal_differs alpha_enum n P a0 Heq).

    (* But P IS alpha_diagonal_pred alpha_enum n *)
    unfold P.
    exact (H_contra a0).
  Qed.

End DiagonalPrep.

