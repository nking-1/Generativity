(*  GenerativeType: The Time-Indexed Type
   
    GenerativeType adds a temporal dimension to AlphaType.
    At t=0, it contains ALL predicates and their negations (primordial unity).
    Time allows paradoxes to separate (P at t1, ¬P at t2).
*)

Require Import DAO.Core.AlphaType.
Require Import Stdlib.Arith.PeanoNat.

(** ** Definition of GenerativeType *)

Class GenerativeType (Alpha : AlphaType) := {
  (** Time-indexed containment of Alpha predicates *)
  contains : nat -> (Alphacarrier -> Prop) -> Prop;
  
  (** The impossible is always contained (it's the anchor) *)
  impossible_always : forall t, contains t omega_veil;
  
  (** Backward containment - what's true later was true earlier *)
  contains_backward : forall m n P, m <= n -> contains n P -> contains m P;
  
  (** Self-reference through Alpha predicates *)
  self_ref_pred_embed : ((Alphacarrier -> Prop) -> Prop) -> (Alphacarrier -> Prop);
  self_ref_pred_embed_correct : 
    forall P : (Alphacarrier -> Prop) -> Prop, 
    P (self_ref_pred_embed P);
  
  (** Generation with temporal awareness *)
  self_ref_generation_exists : 
    forall P : (Alphacarrier -> Prop) -> Prop, 
    forall t : nat, 
    exists n : nat, t <= n /\ contains n (self_ref_pred_embed P)
}.

