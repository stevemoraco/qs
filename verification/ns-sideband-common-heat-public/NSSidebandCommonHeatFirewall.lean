import Mathlib

namespace NSSidebandCommonHeatFirewall

/-- In the frozen-parent scalar principal system, the common absolute heat
`mu` cancels from the numerator of the sideband-to-active ratio derivative.
This is the finite algebraic core behind the differential-gap correction. -/
theorem common_heat_cancels_in_cross_numerator
    {mu delta g h y z ydot zdot : ℝ}
    (hy : ydot = (g - mu) * y)
    (hz : zdot = -(mu + delta) * z + h * y) :
    zdot * y - z * ydot = (h * y - (g + delta) * z) * y := by
  rw [hy, hz]
  ring

/-- The wrong-sign sideband and active high carrier differ in squared
frequency by exactly `8E`, not by the full high-shell square `H`. -/
theorem exact_sideband_active_frequency_gap {E H : ℝ} :
    (9 * E + H) - (E + H) = 8 * E := by
  ring

/-- The optimal principal coefficients have reciprocal square factors:
if the sideband source is sqrt(2) times the active growth coefficient and the
return coefficient is 1/sqrt(2) times the desired coefficient, then the
combined feedback prefactor has exactly the desired square. -/
theorem optimal_coefficients_leave_unit_feedback_square
    {c d g h : ℝ}
    (hreturn : 2 * d ^ 2 = c ^ 2)
    (hsource : h ^ 2 = 2 * g ^ 2) :
    (d * h) ^ 2 = (c * g) ^ 2 := by
  calc
    (d * h) ^ 2 = d ^ 2 * h ^ 2 := by ring
    _ = d ^ 2 * (2 * g ^ 2) := by rw [hsource]
    _ = (2 * d ^ 2) * g ^ 2 := by ring
    _ = c ^ 2 * g ^ 2 := by rw [hreturn]
    _ = (c * g) ^ 2 := by ring

/-- If a drive is bounded by the parent-viscous scale while the child heat is
strictly larger, the intended child cannot have positive scalar growth. -/
theorem small_parent_tube_precludes_child_activation
    {drive parentBudget childHeat : ℝ}
    (hdrive : drive ≤ parentBudget)
    (hgap : parentBudget < childHeat) :
    drive - childHeat < 0 := by
  linarith

/-- The viscous Palasek source window `b>1`, `beta>2b` forces `beta>2`, so
its amplifier rate outruns every parent-scale `N^2` differential heat gap. -/
theorem palasek_window_implies_beta_gt_two
    {b beta : ℝ}
    (hb : 1 < b)
    (hbeta : 2 * b < beta) :
    2 < beta := by
  linarith

/-- The elementary rational part of the one-amplifier-time response bound:
for a differential-gap ratio `q` in `[0,1]`, `1/(2+q) >= 1/3`. -/
theorem one_amplifier_time_rational_floor
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (1 : ℝ) / 3 ≤ 1 / (2 + q) := by
  have hden : 0 < 2 + q := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Exact source-faithful rational point used in the packet bank. -/
theorem live_point_is_inside_viscous_source_window :
    (1 : ℚ) < 17 / 16 ∧
      17 / 16 < (9 / 4 : ℚ) / 2 ∧
      2 * (17 / 16 : ℚ) < 35 / 16 ∧
      (35 / 16 : ℚ) < 9 / 4 := by
  norm_num

/-- At the live point, the source amplitude exceeds the parent fast tube by
`N^(3/16)`. -/
theorem live_source_over_tube_exponent :
    (35 / 16 : ℚ) - 2 = 3 / 16 := by
  norm_num

/-- At the live point, the source drive exceeds the child absolute heat by
`N^(1/16)`. -/
theorem live_drive_over_child_heat_exponent :
    (35 / 16 : ℚ) - 2 * (17 / 16) = 1 / 16 := by
  norm_num

/-- At the live point, the differential sideband heat gap divided by the
source drive is `N^(-3/16)`. -/
theorem live_relative_heat_over_drive_exponent :
    (2 : ℚ) - 35 / 16 = -(3 / 16) := by
  norm_num

/-- The absolute-heat slaving factor advertised in the parent branch would be
`(N/K)^2=N^(-1/8)` at the live point. -/
theorem live_claimed_absolute_slaving_exponent :
    (2 : ℚ) - 2 * (17 / 16) = -(1 / 8) := by
  norm_num

#print axioms common_heat_cancels_in_cross_numerator
#print axioms exact_sideband_active_frequency_gap
#print axioms optimal_coefficients_leave_unit_feedback_square
#print axioms small_parent_tube_precludes_child_activation
#print axioms palasek_window_implies_beta_gt_two
#print axioms one_amplifier_time_rational_floor
#print axioms live_point_is_inside_viscous_source_window
#print axioms live_source_over_tube_exponent
#print axioms live_drive_over_child_heat_exponent
#print axioms live_relative_heat_over_drive_exponent
#print axioms live_claimed_absolute_slaving_exponent

end NSSidebandCommonHeatFirewall
