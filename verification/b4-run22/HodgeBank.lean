import Mathlib

namespace B2Round51NewestSurvivorFirewalls

theorem rh_null_direction_counterexample (M : ℝ) :
    ∃ t : ℝ, (0 : ℝ) * t ^ 2 - 2 * t < -M := by
  refine ⟨(M + 1) / 2, ?_⟩
  ring_nf
  linarith

def d23SplitMoment (j : ℕ) : ℤ :=
  (-3) * (-1) ^ j + 6 * 1 ^ j + (-3) * 5 ^ j + 1 * 7 ^ j

theorem hodge_moment_five : d23SplitMoment 5 = 7441 := by
  norm_num [d23SplitMoment]

theorem hodge_recurrence_extrapolation_counterexample :
    d23SplitMoment 5 ≠ (-23) * d23SplitMoment 3 := by
  norm_num [d23SplitMoment]

theorem ns_counted_debit_counterexample (N : ℕ) (hN : 0 < N) :
    0 < (1 / (N : ℝ)) ∧ (N : ℝ) * (1 / (N : ℝ)) = 1 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · exact one_div_pos.mpr hNr
  · field_simp [ne_of_gt hNr]

theorem bsd_integer_domain_counterexample :
    ∃ a b t tK h L : ℤ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ t ∧ 0 ≤ tK ∧ 0 ≤ h ∧
      2 * (h - t) = (a - t) + (b - tK) ∧
      L = (a - t) + (b - tK) ∧ L < 0 := by
  refine ⟨0, 0, 1, 1, 0, -2, ?_⟩
  norm_num

theorem round51_all_four_checks :
    (∀ M : ℝ, ∃ t : ℝ, (0 : ℝ) * t ^ 2 - 2 * t < -M) ∧
    d23SplitMoment 5 ≠ (-23) * d23SplitMoment 3 ∧
    (∀ N : ℕ, 0 < N →
      0 < (1 / (N : ℝ)) ∧ (N : ℝ) * (1 / (N : ℝ)) = 1) ∧
    (∃ a b t tK h L : ℤ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ t ∧ 0 ≤ tK ∧ 0 ≤ h ∧
      2 * (h - t) = (a - t) + (b - tK) ∧
      L = (a - t) + (b - tK) ∧ L < 0) := by
  refine ⟨rh_null_direction_counterexample,
    hodge_recurrence_extrapolation_counterexample, ?_,
    bsd_integer_domain_counterexample⟩
  intro N hN
  exact ns_counted_debit_counterexample N hN

#print axioms hodge_moment_five
#print axioms hodge_recurrence_extrapolation_counterexample
#print axioms round51_all_four_checks

end B2Round51NewestSurvivorFirewalls
