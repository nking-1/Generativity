Require Import DAO.Core.ClassicalAlphaType.
Require Import DAO.Core.ClassicalAlphaProperties.

Module ClassicalAlphaAPI.
  
  (* Re-export the most commonly used definitions *)
  Definition pred_equiv {H_N: ClassicalAlphaType} := @ClassicalAlphaProperties.Predicates.pred_equiv H_N.
  Definition AlphaPred {H_alpha: ClassicalAlphaType} := @ClassicalAlphaProperties.Helpers.AlphaPred H_alpha.
  Definition classical_veil_is_impossible {H_N: ClassicalAlphaType} := @ClassicalAlphaProperties.Core.classical_veil_is_impossible H_N.
  Definition classical_veil_unique {H_N: ClassicalAlphaType} := @ClassicalAlphaProperties.Core.classical_veil_unique H_N.
  Definition the_necessary {H_alpha: ClassicalAlphaType} := @ClassicalAlphaProperties.Helpers.the_necessary H_alpha.
  Definition witness_not_impossible {H_N: ClassicalAlphaType} := @ClassicalAlphaProperties.Helpers.witness_not_impossible H_N.
  Definition everything_possible_except_one {H_N: ClassicalAlphaType} := @ClassicalAlphaProperties.Predicates.everything_possible_except_one H_N.
  Definition alpha_constant_decision {H_N: ClassicalAlphaType} := @alpha_constant_decision H_N.
  Definition alpha_double_negation_elimination {H_N: ClassicalAlphaType} := @ClassicalAlphaProperties.ClassicalLogic.alpha_double_negation_elimination H_N.
  
End ClassicalAlphaAPI.