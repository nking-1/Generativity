(** * Core Module - Re-exports all core DAO types
    
    This module provides a single import point for all the core types
    in the DAO framework: OmegaType, AlphaType, NomegaType, and GenerativeType.
*)

(** Re-export all core types *)
Require Export DAO.Core.OmegaType.
Require Export DAO.Core.AlphaType.
Require Export DAO.Core.NomegaType.
Require Export DAO.Core.GenerativeType.

(** ** The Triviality Bridge
    
    Both OmegaType and NomegaType are trivial - they can prove anything.
    This theorem shows their fundamental equivalence despite their opposite natures.
*)

Section TrivialityBridge.
  
  (** Both Omega and Nomega can prove any proposition about their carriers *)
  Theorem omega_nomega_equivalence :
    forall {O : OmegaType} {N : NomegaType},
    (* Both can prove any proposition about their carriers *)
    (forall (P : Omegacarrier -> Prop) (x : Omegacarrier), P x) /\
    (forall (Q : Nomegacarrier -> Prop) (y : Nomegacarrier), Q y).
  Proof.
    split.
    - (* Omega case: we have P x and ~P x *)
      exact omega_proves_anything.
    - (* Nomega case: from any y we get False *)
      exact nomega_proves_anything.
  Qed.
  
End TrivialityBridge.

(** ** The DAO Framework Summary
    
    - OmegaType: Complete but paradoxical (contains everything)
    - NomegaType: Empty but equally trivial (contains nothing) 
    - AlphaType: Consistent but incomplete (omega_veil maintains structure)
    - GenerativeType: Adds time dimension to resolve paradoxes temporally
    
    The omega_veil boundary prevents the collapse from Alpha to Omega/Nomega,
    maintaining the gradient that enables mathematics and meaning.
*)