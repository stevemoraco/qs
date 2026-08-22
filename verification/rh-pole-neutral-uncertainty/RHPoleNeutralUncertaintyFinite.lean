import Mathlib

namespace RHPoleNeutralUncertaintyFinite

/-- The two interpolation coefficients exactly reproduce the value of an
exponential at the origin. -/
theorem pole_interpolation_value (s : ℂ) :
    ((1 / 2 : ℂ) + s) + ((1 / 2 : ℂ) - s) = 1 := by
  ring

/-- The same two coefficients exactly reproduce the first derivative of an
exponential at the origin. -/
theorem pole_interpolation_derivative (s : ℂ) :
    (((1 / 2 : ℂ) + s) / 2) - (((1 / 2 : ℂ) - s) / 2) = s := by
  ring

/-- Polynomial core of `∫_{-h}^h u^4 du = 2 h^5 / 5`. -/
theorem quartic_interval_moment_numerator (h : ℝ) :
    h ^ 5 - (-h) ^ 5 = 2 * h ^ 5 := by
  ring

/-- Finite scalar composition of a Cauchy--Schwarz response bound with the
second-order interpolation-residual budget. -/
theorem cauchy_residual_response_budget
    {Q q r B h : ℝ}
    (hQ : 0 ≤ Q) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hcs : Q ≤ q * r)
    (hres : r ^ 2 ≤ B ^ 2 * h ^ 5 / 10) :
    Q ^ 2 ≤ B ^ 2 * h ^ 5 * q ^ 2 / 10 := by
  have hcs_sq : Q ^ 2 ≤ (q * r) ^ 2 := by
    nlinarith
  calc
    Q ^ 2 ≤ (q * r) ^ 2 := hcs_sq
    _ = q ^ 2 * r ^ 2 := by ring
    _ ≤ q ^ 2 * (B ^ 2 * h ^ 5 / 10) :=
      mul_le_mul_of_nonneg_left hres (sq_nonneg q)
    _ = B ^ 2 * h ^ 5 * q ^ 2 / 10 := by ring

/-- A fixed nonnegative response forces the exact inverse-fifth-power energy
lower bound once the analytic response budget has been supplied. -/
theorem fixed_response_forces_fifth_power_energy
    {κ Q B h E : ℝ}
    (hκ : 0 ≤ κ) (hresponse : κ ≤ Q)
    (hB : 0 < B) (hh : 0 < h)
    (hbudget : Q ^ 2 ≤ B ^ 2 * h ^ 5 * E / 10) :
    10 * κ ^ 2 / (B ^ 2 * h ^ 5) ≤ E := by
  have hQ : 0 ≤ Q := le_trans hκ hresponse
  have hkQ : κ ^ 2 ≤ Q ^ 2 := by
    nlinarith
  have hden : 0 < B ^ 2 * h ^ 5 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

/-- For a unit-energy channel, the response budget is equivalently a
fifth-power ceiling. -/
theorem unit_energy_response_ceiling
    {Q B h : ℝ}
    (hbudget : Q ^ 2 ≤ B ^ 2 * h ^ 5 / 10) :
    10 * Q ^ 2 ≤ B ^ 2 * h ^ 5 := by
  nlinarith

/-- Exact exponential ledger for the universal unit-energy response ceiling
at shrink rate `c` and spectral depth `δ`. -/
theorem universal_mode_exponent_identity (c δ T : ℝ) :
    (Real.exp (-c * T)) ^ 5 * Real.exp (2 * δ * T) =
      Real.exp ((2 * δ - 5 * c) * T) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- Any depth below the universal `5c/2` threshold is bounded after
unit-energy normalization. -/
theorem universal_shallow_mode_bounded
    {c δ T : ℝ} (hT : 0 ≤ T) (hdepth : 2 * δ ≤ 5 * c) :
    (Real.exp (-c * T)) ^ 5 * Real.exp (2 * δ * T) ≤ 1 := by
  rw [universal_mode_exponent_identity]
  have hexponent : (2 * δ - 5 * c) * T ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdepth) hT
  simpa using (Real.exp_le_one_iff.mpr hexponent)

#print axioms pole_interpolation_value
#print axioms pole_interpolation_derivative
#print axioms quartic_interval_moment_numerator
#print axioms cauchy_residual_response_budget
#print axioms fixed_response_forces_fifth_power_energy
#print axioms unit_energy_response_ceiling
#print axioms universal_mode_exponent_identity
#print axioms universal_shallow_mode_bounded

end RHPoleNeutralUncertaintyFinite
