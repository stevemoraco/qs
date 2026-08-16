import Mathlib

namespace Millennium.YangMills

/-!
# Compact optical zero-free denominator firewall

The joint compact/optical repair needs a complex optical tube, not merely a
positive real denominator.  These finite lemmas isolate the exact scalar step:
if a normalized complex denominator stays inside the open unit ball around
`1`, then it cannot vanish.  A half-ball gives a quantitative norm floor.

The final theorem packages the common polymer-style situation in which the
complex denominator differs from `1` by at most `exp δ - 1` and the total
complex interaction budget satisfies `δ < log 2`.

This file is finite complex/real analysis only.  It does not prove Kirk's
post-compact holomorphic activity row, BKAR admission, Yang--Mills mass gap,
OS reconstruction, or a Clay theorem.
-/

/-- A complex number inside the open unit ball around `1` is nonzero. -/
theorem complex_ne_zero_of_norm_sub_one_lt_one
    (z : ℂ)
    (h : ‖z - 1‖ < (1 : ℝ)) :
    z ≠ 0 := by
  intro hz
  subst z
  norm_num at h

/-- If a complex denominator is within `1/2` of `1`, its norm is at least
`1/2`.  This is the quantitative form needed for a uniform inverse bound on a
smaller optical tube. -/
theorem complex_norm_ge_half_of_norm_sub_one_le_half
    (z : ℂ)
    (h : ‖z - 1‖ ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 2 ≤ ‖z‖ := by
  have htri : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) - z‖ + ‖z‖ := by
    have hadd := norm_add_le ((1 : ℂ) - z) z
    simpa using hadd
  have hsymm : ‖(1 : ℂ) - z‖ = ‖z - 1‖ := by
    rw [show (1 : ℂ) - z = -(z - 1) by ring]
    simp
  rw [hsymm] at htri
  norm_num at htri
  linarith

/-- A real exponential error budget is strictly below one whenever the total
budget is below `log 2`. -/
theorem exp_sub_one_lt_one_of_lt_log_two
    (δ : ℝ)
    (hδ : δ < Real.log 2) :
    Real.exp δ - 1 < 1 := by
  have hExp : Real.exp δ < (2 : ℝ) := by
    have h := Real.exp_lt_exp.mpr hδ
    simpa using h
  linarith

/-- Polymer-style zero-free criterion: if a normalized complex denominator is
within `exp δ - 1` of `1` and `δ < log 2`, then it cannot vanish. -/
theorem complex_denominator_nonzero_of_exp_error
    (z : ℂ)
    (δ : ℝ)
    (hδ : δ < Real.log 2)
    (hz : ‖z - 1‖ ≤ Real.exp δ - 1) :
    z ≠ 0 := by
  apply complex_ne_zero_of_norm_sub_one_lt_one z
  exact lt_of_le_of_lt hz (exp_sub_one_lt_one_of_lt_log_two δ hδ)

#print axioms complex_ne_zero_of_norm_sub_one_lt_one
#print axioms complex_norm_ge_half_of_norm_sub_one_le_half
#print axioms exp_sub_one_lt_one_of_lt_log_two
#print axioms complex_denominator_nonzero_of_exp_error

end Millennium.YangMills
