import Mathlib

namespace MillenniumRun14

private theorem eighth_power_lower_of_quarter_le
    (x : ℝ) (h : (1 / 4 : ℝ) ≤ x) :
    (1 / 65536 : ℝ) ≤ x ^ 8 := by
  have h1 : 0 ≤ x - (1 / 4 : ℝ) := by linarith
  have h2 : 0 ≤ x + (1 / 4 : ℝ) := by linarith
  have hp2 : 0 ≤ (x - (1 / 4 : ℝ)) * (x + (1 / 4 : ℝ)) :=
    mul_nonneg h1 h2
  have hx2 : (1 / 16 : ℝ) ≤ x ^ 2 := by
    nlinarith
  have h3 : 0 ≤ x ^ 2 - (1 / 16 : ℝ) := by linarith
  have h4 : 0 ≤ x ^ 2 + (1 / 16 : ℝ) := by
    nlinarith [sq_nonneg x]
  have hp4 : 0 ≤ (x ^ 2 - (1 / 16 : ℝ)) * (x ^ 2 + (1 / 16 : ℝ)) :=
    mul_nonneg h3 h4
  have hx4 : (1 / 256 : ℝ) ≤ x ^ 4 := by
    nlinarith
  have h5 : 0 ≤ x ^ 4 - (1 / 256 : ℝ) := by linarith
  have h6 : 0 ≤ x ^ 4 + (1 / 256 : ℝ) := by
    nlinarith [sq_nonneg (x ^ 2)]
  have hp8 : 0 ≤ (x ^ 4 - (1 / 256 : ℝ)) * (x ^ 4 + (1 / 256 : ℝ)) :=
    mul_nonneg h5 h6
  nlinarith

private theorem sixteenth_power_lower_of_half_le
    (x : ℝ) (h : (1 / 2 : ℝ) ≤ x) :
    (1 / 65536 : ℝ) ≤ x ^ 16 := by
  have h8 : (1 / 256 : ℝ) ≤ x ^ 8 := by
    have hquarter : (1 / 4 : ℝ) ≤ x := by linarith
    have hbase := eighth_power_lower_of_quarter_le x hquarter
    nlinarith
  have h1 : 0 ≤ x ^ 8 - (1 / 256 : ℝ) := by linarith
  have h2 : 0 ≤ x ^ 8 + (1 / 256 : ℝ) := by
    nlinarith [sq_nonneg (x ^ 4)]
  have hp : 0 ≤ (x ^ 8 - (1 / 256 : ℝ)) * (x ^ 8 + (1 / 256 : ℝ)) :=
    mul_nonneg h1 h2
  nlinarith

/-- Two rationally related refinement scales have a uniform joint frame floor. -/
theorem two_scale_frame_scalar_lower (u : ℝ) (hu0 : 0 ≤ u) :
    (1 / 65536 : ℝ) ≤ u ^ 8 + (2 * u - 1) ^ 16 := by
  by_cases h : (1 / 4 : ℝ) ≤ u
  · have hu8 := eighth_power_lower_of_quarter_le u h
    have hnon : 0 ≤ (2 * u - 1) ^ 16 := by positivity
    linarith
  · have hv : (1 / 2 : ℝ) ≤ 1 - 2 * u := by linarith
    have hv16 := sixteenth_power_lower_of_half_le (1 - 2 * u) hv
    have heq : (2 * u - 1) ^ 16 = (1 - 2 * u) ^ 16 := by ring
    have hnon : 0 ≤ u ^ 8 := by positivity
    rw [heq]
    linarith

end MillenniumRun14
