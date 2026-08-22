import Mathlib

namespace RHBraid

/-- Exact conversion between the Cramér mean-square exponent and horizontal
zero depth. -/
theorem cramer_exponent_depth_identity
    (beta theta kappa : ℝ)
    (hbeta : beta = (1 / 2 : ℝ) + theta)
    (hkappa : kappa = 1 + 2 * beta) :
    kappa = 2 + 2 * theta := by
  norm_num [hbeta] at hkappa ⊢
  linarith

/-- A mean-square exponent `2+eta` gives the half-width zero-free bound. -/
theorem cramer_power_zero_free
    (theta eta : ℝ)
    (h : 2 + 2 * theta ≤ 2 + eta) :
    theta ≤ eta / 2 := by
  linarith

/-- The fixed-window and Cramér exponents differ by exactly two. -/
theorem filtered_cramer_exponent_shift
    (theta filtered cramer : ℝ)
    (hf : filtered = 2 * theta)
    (hc : cramer = 2 + 2 * theta) :
    filtered = cramer - 2 := by
  linarith

/-- A putative exponent below the pole-forced threshold gives the strict
half-plane opening used by the dyadic Mellin argument. -/
theorem pole_threshold_opening
    (kappa beta : ℝ)
    (h : kappa < 1 + 2 * beta) :
    kappa / 2 - 1 / 2 < beta := by
  linarith

end RHBraid
