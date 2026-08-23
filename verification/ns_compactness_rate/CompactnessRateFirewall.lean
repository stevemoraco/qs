import Mathlib

/-!
# Compactness does not imply a quadratic defect rate

This file formalizes the scalar counterexample to the implication

  compact domain + continuous nonnegative defect + classified zero set
    => distance^2 <= C * defect.

The defect `x^4` on `[0,1]` is continuous, nonnegative, and vanishes exactly at
zero, but no uniform constant controls `x^2` by `C*x^4`.

This is a proof firewall only. It does not formalize Navier--Stokes solutions,
angular measures, interaction defects, or global regularity.
-/

namespace Millennium.NavierStokes.CompactnessRateFirewall

/-- The scalar quartic defect. -/
def quarticDefect (x : ℝ) : ℝ := x ^ 4

/-- The quartic defect is continuous. -/
theorem quarticDefect_continuous : Continuous quarticDefect := by
  fun_prop

/-- The quartic defect is nonnegative. -/
theorem quarticDefect_nonneg (x : ℝ) : 0 ≤ quarticDefect x := by
  positivity

/-- The zero set of the quartic defect is exactly `{0}`. -/
theorem quarticDefect_zero_iff (x : ℝ) : quarticDefect x = 0 ↔ x = 0 := by
  simp [quarticDefect]

/-- No constant gives a quadratic error bound for the quartic defect on the
compact interval `[0,1]`. -/
theorem no_uniform_quadratic_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ C * quarticDefect x := by
  rintro ⟨C, hC, hbound⟩
  let x : ℝ := 1 / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hxpos : 0 < x := by
    exact one_div_pos.mpr hden
  have hxidentity : x * (C + 1) = 1 := by
    dsimp [x]
    field_simp
  have hxle : x ≤ 1 := by
    have hCx : 0 ≤ C * x := mul_nonneg hC hxpos.le
    nlinarith [hxidentity]
  have hraw := hbound x hxpos.le hxle
  have hb : x ^ 2 ≤ C * x ^ 4 := by
    simpa [quarticDefect] using hraw
  have hxsqpos : 0 < x ^ 2 := sq_pos_of_pos hxpos
  have hxsqle : x ^ 2 ≤ x := by
    nlinarith
  have hCxlt : C * x < 1 := by
    nlinarith [hxidentity]
  have hCx2le : C * x ^ 2 ≤ C * x :=
    mul_le_mul_of_nonneg_left hxsqle hC
  have hCx2lt : C * x ^ 2 < 1 := lt_of_le_of_lt hCx2le hCxlt
  have hstrict : C * x ^ 4 < x ^ 2 := by
    calc
      C * x ^ 4 = x ^ 2 * (C * x ^ 2) := by ring
      _ < x ^ 2 * 1 := mul_lt_mul_of_pos_left hCx2lt hxsqpos
      _ = x ^ 2 := by ring
  exact (not_lt_of_ge hb) hstrict

/-- A continuous nonnegative function can have the correct zero set on a compact
interval while failing every quadratic distance-to-zero estimate. -/
theorem compact_zero_set_data_do_not_force_quadratic_rate :
    Continuous quarticDefect ∧
    (∀ x : ℝ, 0 ≤ quarticDefect x) ∧
    (∀ x : ℝ, quarticDefect x = 0 ↔ x = 0) ∧
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ C * quarticDefect x := by
  exact ⟨quarticDefect_continuous, quarticDefect_nonneg,
    quarticDefect_zero_iff, no_uniform_quadratic_bound⟩

/-- The correct quantitative replacement is an explicit modulus hypothesis;
once supplied, it can of course be consumed directly. -/
theorem quadratic_rate_requires_quantitative_input
    (d : ℝ → ℝ) (C : ℝ)
    (hquant : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ C * d x) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ^ 2 ≤ C * d x := by
  exact hquant

#print axioms quarticDefect_continuous
#print axioms quarticDefect_nonneg
#print axioms quarticDefect_zero_iff
#print axioms no_uniform_quadratic_bound
#print axioms compact_zero_set_data_do_not_force_quadratic_rate
#print axioms quadratic_rate_requires_quantitative_input

end Millennium.NavierStokes.CompactnessRateFirewall
