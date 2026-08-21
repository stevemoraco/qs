import Mathlib

namespace Millennium.NavierStokes.C486

theorem scalar_feasible_iff (B : ℝ) :
    (∃ r : ℝ, 0 ≤ r ∧ r ^ 2 + (1 / 4 : ℝ) ≤ B * r) ↔ 1 ≤ B := by
  constructor
  · rintro ⟨r, hr, hineq⟩
    have hrpos : 0 < r := by
      by_contra hnot
      have hrzero : r = 0 := le_antisymm (le_of_not_gt hnot) hr
      rw [hrzero] at hineq
      norm_num at hineq
    have hbase : r ≤ r ^ 2 + (1 / 4 : ℝ) := by
      nlinarith [sq_nonneg (r - (1 / 2 : ℝ))]
    have hmul : r ≤ B * r := hbase.trans hineq
    nlinarith
  · intro hB
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    nlinarith

theorem endpoint_ratio_unique {r : ℝ}
    (hineq : r ^ 2 + (1 / 4 : ℝ) ≤ r) :
    r = 1 / 2 := by
  nlinarith [sq_nonneg (r - (1 / 2 : ℝ))]

theorem half_ratio_feasible {B : ℝ} (hB : 1 ≤ B) :
    (1 / 2 : ℝ) ^ 2 + (1 / 4 : ℝ) ≤ B * (1 / 2 : ℝ) := by
  nlinarith

#print axioms scalar_feasible_iff
#print axioms endpoint_ratio_unique
#print axioms half_ratio_feasible

end Millennium.NavierStokes.C486
