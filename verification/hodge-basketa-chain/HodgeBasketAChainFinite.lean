import Mathlib

namespace HodgeQ1A8BasketAMultipleFibreChainFiniteCore

/-!
Finite arithmetic shadow of the q1a8 basket-A multiple-fibre-chain closure.
The geometric K3, pencil, proximity, and divisor-restriction inputs remain
outside this file.
-/

theorem effective_residual_forces_k_le_six
    (k b : ℤ) (hb : b = 6 - k) (hb_nonneg : 0 ≤ b) :
    k ≤ 6 := by
  linarith

theorem horizontal_branch_forces_k_le_two
    (k b : ℤ) (hb : b = 6 - k) (hcost : 4 ≤ b) :
    k ≤ 2 := by
  linarith

theorem no_residual_branch_chain_impossible
    (k : ℤ) (heffective : k ≤ 6) (hterminal : 2 ≤ k - 6) :
    False := by
  linarith

theorem one_residual_branch_chain_impossible
    (k : ℤ) (hbranch : k ≤ 2) (hterminal : 2 ≤ k - 2) :
    False := by
  linarith

theorem basketA_chain_arithmetic_firewall
    (k : ℤ)
    (heffective : k ≤ 6)
    (hcases : (2 ≤ k - 6) ∨ (k ≤ 2 ∧ 2 ≤ k - 2)) :
    False := by
  rcases hcases with hmiss | hpass
  · exact no_residual_branch_chain_impossible k heffective hmiss
  · exact one_residual_branch_chain_impossible k hpass.1 hpass.2

theorem source_divisor_intersection_ledger :
    (3 : ℤ) * 3 * (-2) + 2 * 3 * 6 = 18 ∧
    (3 : ℤ) = 3 := by
  norm_num

#print axioms effective_residual_forces_k_le_six
#print axioms horizontal_branch_forces_k_le_two
#print axioms no_residual_branch_chain_impossible
#print axioms one_residual_branch_chain_impossible
#print axioms basketA_chain_arithmetic_firewall
#print axioms source_divisor_intersection_ledger

end HodgeQ1A8BasketAMultipleFibreChainFiniteCore
