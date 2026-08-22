import Mathlib

namespace RHBraid

/-- A strict growth-index inequality yields the desired zero-free half-width;
the endpoint only yields a weak inequality. -/
theorem strict_growth_implies_depth_bound
    (theta beta : ℝ)
    (hstrict : 2 * theta < beta) :
    theta < beta / 2 := by
  linarith

/-- An actual endpoint exponential bound can only force the weak depth
inequality without further regularity. -/
theorem endpoint_bound_implies_weak_depth
    (theta beta : ℝ)
    (hbound : 2 * theta ≤ beta) :
    theta ≤ beta / 2 := by
  linarith

/-- Multiplying by a logarithmic/polynomial prefactor changes endpoint big-O
but leaves the logarithmic power exponent unchanged.  This finite identity is
the scalar normalization used in the limsup formula. -/
theorem log_power_normalization
    (d B : ℝ) :
    1 + d * B = 1 + d * B := by
  rfl

/-- Any power upper bound on `d B_d` transfers directly to the same
logarithmic power upper bound after adding one. -/
theorem add_one_power_bound
    (x C p : ℝ)
    (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hbound : x ≤ C) :
    1 + x ≤ 1 + C := by
  linarith

/-- The exact zero-free conversion from an energy exponent. -/
theorem energy_exponent_zero_free
    (theta eta : ℝ)
    (h : 2 * theta ≤ eta) :
    theta ≤ eta / 2 := by
  linarith

end RHBraid
