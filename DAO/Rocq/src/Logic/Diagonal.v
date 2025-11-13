(** * Diagonal.v: Diagonal Arguments in DAO Framework
    
    This module implements diagonal arguments showing:
    - Alpha cannot enumerate its own predicates (incompleteness)
    - Omega can witness any diagonal construction (completeness)
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.OmegaProperties.

Module Diagonal.

  (* ================================================================ *)
  (** ** Main Definitions and Theorems *)

  Module Main.
    
    (** The diagonal construction: flips the nth predicate at position n *)
    Definition diagonal {A : Type} (enum : nat -> option (A -> Prop)) 
      : nat -> A -> Prop :=
      fun n => match enum n with
      | Some P => fun a => ~ P a
      | None => fun _ => True
      end.
    
    (** Core theorem: diagonal differs from enumerated predicates *)
    Theorem diagonal_differs {A : Type} :
      forall (enum : nat -> option (A -> Prop)) n P a,
      enum n = Some P ->
      ~ (P a <-> diagonal enum n a).
    Proof.
      intros enum n P a Henum H_iff.
      unfold diagonal in H_iff.
      rewrite Henum in H_iff.
      destruct H_iff as [H1 H2].
      assert (HnP : ~ P a) by (intro HP; apply (H1 HP); exact HP).
      assert (HP : P a) by (apply H2; exact HnP).
      exact (HnP HP).
    Qed.
    
  End Main.

  (* ================================================================ *)
  (** ** Alpha Diagonal Properties *)

  Module Alpha.
    
    Section Properties.
      Context `{Alpha : AlphaType}.
      Variable enum : nat -> option (Alphacarrier -> Prop).
      
      (** Alpha's diagonal predicate *)
      Definition diagonal_pred := Main.diagonal enum.
      
      (** Diagonal differs from any enumerated predicate *)
      Theorem diagonal_differs :
        forall n P a,
        enum n = Some P ->
        ~ (P a <-> diagonal_pred n a).
      Proof.
        exact (Main.diagonal_differs enum).
      Qed.
      
      (** The diagonal is not in the enumeration *)
      Theorem diagonal_not_enumerated :
        forall n,
        enum n <> Some (fun a => diagonal_pred n a).
      Proof.
        intros n Heq.
        assert (H_contra : forall a, 
          diagonal_pred n a <-> diagonal_pred n a)
          by (intro a; split; auto).
        
        pose (P := fun a => diagonal_pred n a).
        destruct alpha_not_empty as [a0 _].
        
        apply (diagonal_differs n P a0 Heq).
        unfold P.
        exact (H_contra a0).
      Qed.
      
    End Properties.
  End Alpha.

  (* ================================================================ *)
  (** ** Omega Diagonal Properties *)

  Module Omega.
    Import Main.

    (** Lift Alpha's diagonal to Omega *)
    Definition om_diagonal {Omega : OmegaType} {Alpha : AlphaType}
      (alpha_enum : nat -> option (Alphacarrier -> Prop))
      (embed : Alphacarrier -> Omegacarrier) : Omegacarrier -> Prop :=
      fun x => exists n a, 
        embed a = x /\ 
        Main.diagonal alpha_enum n a.
    
    Section Properties.
      Context `{Omega : OmegaType} `{Alpha : AlphaType}.
      Variable alpha_enum : nat -> option (Alphacarrier -> Prop).
      Variable embed : Alphacarrier -> Omegacarrier.
      
      (** Omega witnesses the diagonal *)
Theorem diagonal_exists :
  exists x : Omegacarrier, om_diagonal alpha_enum embed x.
Proof.
  apply omega_completeness.
Qed.

(** But Omega also witnesses the negation *)
Theorem diagonal_does_not_exist :
  exists x : Omegacarrier, ~ om_diagonal alpha_enum embed x.
Proof.
  (* The predicate "not om_diagonal" also has a witness in Omega *)
  pose (not_diag := fun x => ~ om_diagonal alpha_enum embed x).
  apply (omega_completeness not_diag).
Qed.

(** Omega witnesses contradictory predicates about the diagonal *)
Theorem omega_diagonal_paradox :
  (exists x : Omegacarrier, om_diagonal alpha_enum embed x) /\
  (exists y : Omegacarrier, ~ om_diagonal alpha_enum embed y).
Proof.
  split.
  - apply diagonal_exists.
  - apply diagonal_does_not_exist.
Qed.

(** Or even stronger: there exists a point satisfying both *)
Theorem omega_witnesses_contradiction :
  exists x : Omegacarrier, 
    om_diagonal alpha_enum embed x /\ ~ om_diagonal alpha_enum embed x.
Proof.
  (* This is just omega_has_paradoxes applied to the diagonal *)
  pose (diag := om_diagonal alpha_enum embed).
  destruct (OmegaProperties.Paradoxes.omega_has_paradoxes diag) as [x Hx].
  exists x.
  exact Hx.
Qed.

      (** The price Omega pays to see everything is to not distinguish truth and falsehood *)
      Theorem diagonal_exists_iff_not_exists :
        exists x : Omegacarrier, om_diagonal alpha_enum embed x <-> ~ exists x : Omegacarrier, om_diagonal alpha_enum embed x.
      Proof.
        apply omega_completeness.
      Qed.
      
      (** Witnesses exist at every index *)
      Theorem diagonal_at_index :
        forall n,
        exists x : Omegacarrier,
        exists a : Alphacarrier,
        embed a = x /\ Main.diagonal alpha_enum n a.
      Proof.
        intro n.
        pose (pred_n := fun x => exists a, embed a = x /\ Main.diagonal alpha_enum n a).
        destruct (omega_completeness pred_n) as [x Hx].
        exists x.
        exact Hx.
      Qed.
      
    End Properties.
  End Omega.

End Diagonal.