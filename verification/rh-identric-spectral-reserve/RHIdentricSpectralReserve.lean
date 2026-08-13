import Mathlib

namespace RHIdentricSpectralReserve

/-- If the identric mean lies below the arithmetic mean and the half-reserve
is nonnegative, then the arrival threshold is strictly safe. -/
theorem safe_of_nonnegative_half_reserve
    {I A T : ℝ}
    (hIA : I < A)
    (hReserve : 0 ≤ T - A) :
    I < T := by
  linarith

/-- If the threshold lies below the geometric mean and the geometric mean
lies below the identric mean, then the arrival is strictly dangerous. -/
theorem dangerous_of_geometric_clearance
    {I G A T : ℝ}
    (hGI : G < I)
    (hClearance : T - A < -(A - G)) :
    T < I := by
  linarith

/-- Algebraic core of the arithmetic/geometric mean gap after writing the
endpoints as squares. -/
theorem root_gap_identity (u v : ℝ) :
    (u ^ 2 + v ^ 2) / 2 - u * v = (v - u) ^ 2 / 2 := by
  ring

/-- Finite algebraic core of the explicit-formula reserve decomposition. -/
theorem spectral_reserve_identity
    {T A H c Z τ ψ : ℝ}
    (hPrimePowerSplit : ψ = A + H)
    (hExplicitFormula : T = ψ + Z + c - τ) :
    T - A = H + c + Z - τ := by
  linarith

/-- The proposed signed zero-sum lower bound makes the spectral reserve
nonnegative. -/
theorem spectral_lower_bound_closes_arrival
    {H c Z τ : ℝ}
    (hLower : -H - c + τ ≤ Z) :
    0 ≤ H + c + Z - τ := by
  linarith

/-- If the reserve falls below a negative clearance, then the zero sum has
crossed the corresponding exact threshold. -/
theorem spectral_failure_forces_threshold_breach
    {H c Z τ η : ℝ}
    (hFailure : H + c + Z - τ < -η) :
    Z < -H - c + τ - η := by
  linarith

#print axioms safe_of_nonnegative_half_reserve
#print axioms dangerous_of_geometric_clearance
#print axioms root_gap_identity
#print axioms spectral_reserve_identity
#print axioms spectral_lower_bound_closes_arrival
#print axioms spectral_failure_forces_threshold_breach

end RHIdentricSpectralReserve
