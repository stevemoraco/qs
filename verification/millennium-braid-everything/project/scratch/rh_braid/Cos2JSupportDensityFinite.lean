import Mathlib

/-!
# Finite bookkeeping for the cos^(2J) support-density budget

These lemmas formalize only the elementary order/arithmetic core of the
support-density self-consistency theorem.  They do not formalize the Fourier
transform, Riemann-von Mangoldt formula, or RH.
-/

namespace RHProof
namespace Cos2JSupportDensity

/-- If a degree-`M` annihilator satisfies `M ≤ 2J`, then the squared
algebraic majorant `|w|^{-2(2J+1-M)}` has power at least `2`. -/
theorem squared_decay_power_ge_two
    (J M : ℕ)
    (hM : M ≤ 2 * J) :
    2 ≤ 2 * ((2 * J + 1) - M) := by
  omega

/-- A strict fractional degree surplus leaves the corresponding linear
reserve in the exponent budget. -/
theorem reserve_from_fraction
    (J M eps : ℝ)
    (hJ : 0 ≤ J)
    (hM : M ≤ (2 - eps) * J) :
    eps * J ≤ 2 * J - M := by
  nlinarith

/-- Exact algebraic identity behind
`2J-M = 2J(1-c*theta/kappa)` when
`M = 2J*c*theta/kappa`. -/
theorem exact_density_reserve_identity
    (J c theta kappa : ℝ) :
    2 * J - (2 * J * (c * theta / kappa)) =
      2 * J * (1 - c * theta / kappa) := by
  ring

/-- A strict support-density surplus `c*theta < kappa` gives a strictly
positive normalized reserve. -/
theorem positive_reserve_of_density_surplus
    (J c theta kappa : ℝ)
    (hJ : 0 < J)
    (hkappa : 0 < kappa)
    (hsurplus : c * theta < kappa) :
    0 < 2 * J * (1 - c * theta / kappa) := by
  have hratio : c * theta / kappa < 1 :=
    (div_lt_one hkappa).2 hsurplus
  have hpos : 0 < 1 - c * theta / kappa := sub_pos.mpr hratio
  positivity

/-- If the normalized annihilator-degree ratio is bounded by
`c*theta/kappa ≤ 1`, then the degree budget `M ≤ 2J` follows. -/
theorem degree_budget_of_density_ratio
    (J M c theta kappa : ℝ)
    (hJ : 0 ≤ J)
    (hkappa : 0 < kappa)
    (hdensity : c * theta ≤ kappa)
    (hM : M ≤ 2 * J * (c * theta / kappa)) :
    M ≤ 2 * J := by
  have hratio : c * theta / kappa ≤ 1 :=
    (div_le_one hkappa).2 hdensity
  have h2J : 0 ≤ 2 * J := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hratio h2J
  calc
    M ≤ 2 * J * (c * theta / kappa) := hM
    _ ≤ 2 * J * 1 := by simpa [mul_assoc] using hscaled
    _ = 2 * J := by ring

end Cos2JSupportDensity
end RHProof
