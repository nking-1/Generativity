(* File for classes and definitions that bridge between Alpha,
   Omega, Generative types *)

Require Import DAO.Core.AlphaType.
Require Import DAO.Core.OmegaType.
Require Import DAO.Core.GenerativeType.

(**
 [OmegaToGenerative] bridges GenerativeType and OmegaType.
 It shows how to embed Alpha predicates into the timeless Omega, 
 and project from Omega back to time-indexed predicates in GenerativeType.
**)
Class OmegaToGenerative (Alpha : AlphaType) (HG : GenerativeType Alpha) (Omega : OmegaType) := {
  project_Omega_gen : Omegacarrier -> (Alphacarrier -> Prop);
  lift_Gen : (Alphacarrier -> Prop) -> Omegacarrier;
  
  (* Key coherence: Omega contains all predicates timelessly, 
     GenerativeType reveals them temporally *)
  projection_coherence_gen : forall (x : Omegacarrier) (t : nat),
    exists (P : Alphacarrier -> Prop), 
    contains t P /\ P = project_Omega_gen x
}.