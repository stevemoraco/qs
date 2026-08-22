import Mathlib

namespace RHBraid

/-- Exact conversion from a Cramér `L^p` exponent to horizontal zero depth. -/
theorem cramer_lp_depth_identity
    (p beta theta kappa : ℝ)
    (hp : p ≠ 0)
    (hbeta : beta = (1 / 2 : ℝ) + theta)
    (hkappa : kappa = 1 + p * beta) :
    theta = (kappa - 1) / p - 1 / 2 := by
  rw [hkappa, hbeta]
  field_simp [hp]
  ring

/-- All fixed positive moment orders have the same normalized depth exponent. -/
theorem normalized_lp_depth_independent
    (p r beta kp kr : ℝ)
    (hp : p ≠ 0) (hr : r ≠ 0)
    (hkp : kp = 1 + p * beta)
    (hkr : kr = 1 + r * beta) :
    (kp - 1) / p = (kr - 1) / r := by
  rw [hkp, hkr]
  field_simp [hp, hr]
  ring

/-- A proposed `L^p` exponent improvement converts to the corresponding
zero-free half-width after subtracting the critical-line baseline. -/
theorem lp_power_zero_free
    (p theta eta : ℝ)
    (hp : 0 < p)
    (h : 1 + p / 2 + p * theta ≤ 1 + p / 2 + p * eta) :
    theta ≤ eta := by
  nlinarith

/-- The Mellin-pole threshold opening used by the Hölder lower bound. -/
theorem lp_pole_threshold_opening
    (p kappa beta : ℝ)
    (hp : 0 < p)
    (h : kappa < 1 + p * beta) :
    (kappa - 1) / p < beta := by
  exact (div_lt_iff₀ hp).2 (by linarith)

end RHBraid
