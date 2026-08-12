import Mathlib

namespace RHShrinkingWindowFinite

/-- The exact energy exponent produced by a fifth-power window penalty and a
spectral mode of depth `δ`.  This is the finite scalar ledger behind the
shrinking-window depth–ultraviolet firewall. -/
theorem exponential_window_depth_identity (c δ T : ℝ) :
    (Real.exp (-c * T)) ^ 5 * Real.exp (2 * δ * T) =
      Real.exp ((2 * δ - 5 * c) * T) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- If the spectral growth `2δ` does not exceed the fifth-power normalization
loss `5c`, then the normalized scalar signal is bounded by one at every
nonnegative height. -/
theorem normalized_signal_bounded
    {c δ T : ℝ} (hT : 0 ≤ T) (hdepth : 2 * δ ≤ 5 * c) :
    (Real.exp (-c * T)) ^ 5 * Real.exp (2 * δ * T) ≤ 1 := by
  rw [exponential_window_depth_identity]
  have hexponent : (2 * δ - 5 * c) * T ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdepth) hT
  calc
    Real.exp ((2 * δ - 5 * c) * T) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hexponent
    _ = 1 := Real.exp_zero

/-- Below the exact threshold, the normalized scalar signal is strictly less
than one at every positive height. -/
theorem normalized_signal_strictly_below_one
    {c δ T : ℝ} (hT : 0 < T) (hdepth : 2 * δ < 5 * c) :
    (Real.exp (-c * T)) ^ 5 * Real.exp (2 * δ * T) < 1 := by
  rw [exponential_window_depth_identity]
  have hexponent : (2 * δ - 5 * c) * T < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hdepth) hT
  simpa using (Real.exp_lt_one_iff.mpr hexponent)

/-- At the boundary `2δ = 5c`, the normalized scalar signal is exactly one. -/
theorem normalized_signal_boundary
    {c δ T : ℝ} (hdepth : 2 * δ = 5 * c) :
    (Real.exp (-c * T)) ^ 5 * Real.exp (2 * δ * T) = 1 := by
  rw [exponential_window_depth_identity]
  have : (2 * δ - 5 * c) * T = 0 := by rw [hdepth]; ring
  rw [this, Real.exp_zero]

/-- Generic rational bounds used by the exact triple-spline normalization
square.  Instantiating `x = h^5` and
`d = 11 h^4 + 40 h^2 + 120` gives
`(640/171) h^5 ≤ C_h⁻¹ ≤ (16/3) h^5` whenever `0 < h ≤ 1`. -/
theorem normalization_square_bounds
    {x d a : ℝ}
    (hx : 0 ≤ x) (hd_lower : 120 ≤ d) (hd_upper : d ≤ 171)
    (ha : a = 640 * x / d) :
    (640 / 171 : ℝ) * x ≤ a ∧ a ≤ (16 / 3 : ℝ) * x := by
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num) hd_lower
  subst a
  constructor
  · apply (le_div_iff₀ hd_pos).2
    have hm := mul_le_mul_of_nonneg_left hd_upper hx
    nlinarith
  · apply (div_le_iff₀ hd_pos).2
    have hm := mul_le_mul_of_nonneg_left hd_lower hx
    nlinarith

/-- The raw fifth-power ultraviolet debt is the inverse of the normalized
fifth-power attenuation. -/
theorem raw_normalized_fifth_power_duality (h : ℝ) (hh : h ≠ 0) :
    (h ^ 5)⁻¹ * h ^ 5 = 1 := by
  exact inv_mul_cancel₀ (pow_ne_zero 5 hh)

#print axioms exponential_window_depth_identity
#print axioms normalized_signal_bounded
#print axioms normalized_signal_strictly_below_one
#print axioms normalized_signal_boundary
#print axioms normalization_square_bounds
#print axioms raw_normalized_fifth_power_duality

end RHShrinkingWindowFinite
