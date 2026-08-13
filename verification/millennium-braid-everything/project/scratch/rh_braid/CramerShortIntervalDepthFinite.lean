import Mathlib

namespace RHBraid

/-- Subtracting the geometric short-interval baseline recovers the same
horizontal depth parameter. -/
theorem short_interval_depth_identity
    (p theta beta depth kappa : ℝ)
    (hp : p ≠ 0)
    (hbeta : beta = (1 / 2 : ℝ) + depth)
    (hkappa : kappa = theta + p * beta) :
    depth = (kappa - theta) / p - 1 / 2 := by
  rw [hkappa, hbeta]
  field_simp [hp]
  ring

/-- A local exponent bound at the critical baseline plus `p*eta` gives the
usual zero-free half-width. -/
theorem short_interval_zero_free
    (p theta depth eta : ℝ)
    (hp : 0 < p)
    (h : theta + p / 2 + p * depth ≤
         theta + p / 2 + p * eta) :
    depth ≤ eta := by
  nlinarith

/-- The dyadic cover exponent adds the number-of-intervals cost `1-theta` to
one local exponent. -/
theorem cover_exponent_accounting
    (theta local : ℝ) :
    (1 - theta) + (theta + local) = 1 + local := by
  ring

/-- Moment order and interval scale both disappear after the natural
normalization. -/
theorem normalized_local_depth_same
    (p r theta phi beta kp kr : ℝ)
    (hp : p ≠ 0) (hr : r ≠ 0)
    (hkp : kp = theta + p * beta)
    (hkr : kr = phi + r * beta) :
    (kp - theta) / p = (kr - phi) / r := by
  rw [hkp, hkr]
  field_simp [hp, hr]
  ring

end RHBraid
