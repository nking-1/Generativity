(** * Rice.v: Rice's Theorem in the DAO Framework
    
    This module proves Rice's theorem using the unrepresentability framework:
    - Non-trivial semantic properties create unrepresentable Omega predicates
    - Therefore they must be undecidable in Alpha's ternary logic
*)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Logic.AlphaTernary.
Require Import DAO.Logic.Unrepresentability.

Module Rice.

  (* ================================================================ *)
  (** ** Core Definitions *)
  (* ================================================================ *)
  
  Section RiceTheorem.
    Context {Alpha : AlphaType} {Omega : OmegaType}.
    Variable embed : Alphacarrier -> Omegacarrier.
    
    (* Basic computation relation *)
    Variable Computes : Alphacarrier -> Alphacarrier -> Alphacarrier -> Prop.
    
    (** Two programs are semantically equivalent if they compute the same function *)
    Definition sem_equiv (p1 p2 : Alphacarrier) : Prop :=
      forall input output, Computes p1 input output <-> Computes p2 input output.
    
    (** A property is semantic if it respects functional equivalence *)
    Definition semantic_property (P : Alphacarrier -> Prop) : Prop :=
      forall p1 p2, sem_equiv p1 p2 -> (P p1 <-> P p2).
    
    (** The Rice omega predicate: programs that witness property flipping *)
    Definition rice_omega (P : Alphacarrier -> Prop) : Omegacarrier -> Prop :=
      fun x => exists p test_prog output,
        embed p = x /\
        Computes p test_prog output /\
        P test_prog /\ ~ P output.
    
    (** The corresponding Alpha predicate *)
    Definition rice_alpha (P : Alphacarrier -> Prop) : Alphacarrier -> Prop :=
      fun a => rice_omega P (embed a).
    
    (* ================================================================ *)
    (** ** Basic Properties *)
    (* ================================================================ *)
    
    (** Rice omega exists by omega completeness *)
    Lemma rice_omega_exists (P : Alphacarrier -> Prop) :
      exists x : Omegacarrier, rice_omega P x.
    Proof.
      apply omega_completeness.
    Qed.
    
    (** Axiom: The Rice diagonal is unrepresentable *)
    (* Future work could prove rice_omega_unrepresentable by showing 
        how semantic properties enable diagonal constructions similar to
        those in the Gödel/Turing proofs *)
    Axiom rice_omega_unrepresentable : forall P : Alphacarrier -> Prop,
      semantic_property P ->
      (exists p, P p) -> 
      (exists p, ~ P p) ->
      ~ Unrepresentability.Core.representable (rice_omega P).
    
    (* ================================================================ *)
    (** ** Main Theorems *)
    (* ================================================================ *)
    
    (** Rice's theorem via the unrepresentability framework *)
    Theorem rice_undecidable (P : Alphacarrier -> Prop) :
      semantic_property P ->
      (exists p, P p) -> 
      (exists p, ~ P p) ->
      (~ exists a, rice_alpha P a) /\ (~ forall a, ~ rice_alpha P a).
    Proof.
      intros Hsem Hyes Hno.
      
      (* Apply the general unrepresentability framework *)
      apply (Unrepresentability.Framework.unrepresentable_implies_undecidable 
               embed (rice_alpha P) (rice_omega P)).
      
      - (* Surjectivity-like property *)
        intros x [p [test [out [Hembed _]]]].
        exists p. exact Hembed.
        
      - (* Show it's an instance of Undecidable_Via_Unrepresentability *)
        unfold Unrepresentability.Framework.Undecidable_Via_Unrepresentability.
        split; [|split].
        
        + (* rice_alpha detects rice_omega through embed *)
          intro a.
          unfold rice_alpha.
          reflexivity.
          
        + (* rice_omega exists *)
          exact (rice_omega_exists P).
          
        + (* rice_omega is not representable *)
          exact (rice_omega_unrepresentable P Hsem Hyes Hno).
    Qed.
    
    (** Rice's theorem in terms of ternary logic *)
    Theorem rice_ternary (P : Alphacarrier -> Prop) :
      semantic_property P ->
      (exists p, P p) -> 
      (exists p, ~ P p) ->
      AlphaTernary.TernaryLogic.AlphaTruth (rice_alpha P).
    Proof.
      intros Hsem Hyes Hno.
      destruct (rice_undecidable P Hsem Hyes Hno) as [H1 H2].
      exact (AlphaTernary.TernaryLogic.Alpha_Undecidable _ H1 H2).
    Qed.
    
    (** Corollary: Semantic properties create undecidability *)
    Corollary semantic_properties_undecidable :
      forall P : Alphacarrier -> Prop,
      semantic_property P ->
      (exists p, P p) -> 
      (exists p, ~ P p) ->
      exists Q : Alphacarrier -> Prop,
        (~ exists a, Q a) /\ (~ forall a, ~ Q a).
    Proof.
      intros P Hsem Hyes Hno.
      exists (rice_alpha P).
      exact (rice_undecidable P Hsem Hyes Hno).
    Qed.
    
  End RiceTheorem.
  
End Rice.