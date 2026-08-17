import Mathlib

/-!
# Yang--Mills root-degree cost firewall

A fixed number of distinguished roots does not by itself contribute one fixed
multiplicative constant to a rooted tree expansion.  If a retained root has
unbounded incident degree and each incident edge costs a fixed factor, that
root cost can grow exponentially with the number of nonroot vertices and can
cancel the nominal nonroot contraction.

This file proves only the finite scalar countermechanism.  It does not
formalize replica--BKAR, Kirk's Banach spaces, Yang--Mills theory, a mass gap,
or a Clay theorem.
-/

namespace Millennium.YangMills.RootDegreeCostFirewall

open scoped BigOperators

def nonrootContraction (n : ℕ) : ℝ := ((1 : ℝ) / 2) ^ n

def oneRootIncidentCost (n : ℕ) : ℝ := (2 : ℝ) ^ n

theorem one_root_degree_cost_cancels_nonroot_contraction (n : ℕ) :
    oneRootIncidentCost n * nonrootContraction n = 1 := by
  simp [oneRootIncidentCost, nonrootContraction, ← mul_pow]

theorem nominal_nonroot_factor_is_subunit :
    (0 : ℝ) ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  norm_num

theorem hostile_rooted_star_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.range N,
      oneRootIncidentCost n * nonrootContraction n) = (N : ℝ) := by
  simp [one_root_degree_cost_cancels_nonroot_contraction]

theorem fixed_root_count_does_not_give_fixed_prefactor (E : ℝ) :
    ∃ N : ℕ,
      E < ∑ n ∈ Finset.range N,
        oneRootIncidentCost n * nonrootContraction n := by
  obtain ⟨N, hN⟩ := exists_nat_gt E
  refine ⟨N, ?_⟩
  rw [hostile_rooted_star_partial_sum]
  exact hN

theorem incident_cost_changes_effective_branch
    (L m : ℝ) (n : ℕ) :
    L ^ n * m ^ n = (L * m) ^ n := by
  exact (mul_pow L m n).symm

theorem effective_factor_at_least_one_has_no_decay
    (L m : ℝ) (n : ℕ)
    (h : 1 ≤ L * m) :
    1 ≤ L ^ n * m ^ n := by
  rw [incident_cost_changes_effective_branch]
  exact one_le_pow₀ h

#print axioms one_root_degree_cost_cancels_nonroot_contraction
#print axioms nominal_nonroot_factor_is_subunit
#print axioms hostile_rooted_star_partial_sum
#print axioms fixed_root_count_does_not_give_fixed_prefactor
#print axioms incident_cost_changes_effective_branch
#print axioms effective_factor_at_least_one_has_no_decay

end Millennium.YangMills.RootDegreeCostFirewall
