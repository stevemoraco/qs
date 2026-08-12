import Mathlib

/-!
# Round 217 Navier--Stokes intrinsic-VMO finite cores

This file formalizes only scalar error budgets, scale identities, a two-core
oscillation lower bound, and the final amplification contradiction.

It does not formalize Calderón--Zygmund operators, commutators, Jones
extension, Lorentz spaces, BMO/VMO, vorticity, spatial analyticity, the
Navier--Stokes equations, or the Clay problem.
-/

namespace Millennium
namespace Round217NavierStokes

/-- If the finitely many near/intermediate annuli and the geometric far tail
each consume half of an error budget, their sum consumes the full budget. -/
theorem annular_commutator_budget_below_epsilon
    (C K beta tail eps : ℝ)
    (hnear : C * (K + 1) * beta ≤ eps / 2)
    (hfar : C * tail ≤ eps / 2) :
    C * ((K + 1) * beta + tail) ≤ eps := by
  nlinarith

/-- The fixed-shell diagonal choice used in the rate-free argument: first
choose a tail budget, then choose the local modulus for that fixed shell. -/
theorem fixed_shell_rate_free_choice
    (C K beta tail eps : ℝ)
    (hC : 0 ≤ C)
    (hK : 0 ≤ K + 1)
    (hbeta : 0 ≤ beta)
    (htail : 0 ≤ tail)
    (heps : 0 < eps)
    (hnear : beta ≤ eps / (2 * C * (K + 1)))
    (hfar : tail ≤ eps / (2 * C))
    (hdenNear : 0 < 2 * C * (K + 1))
    (hdenFar : 0 < 2 * C) :
    C * ((K + 1) * beta + tail) ≤ eps := by
  have hnear' : C * (K + 1) * beta ≤ eps / 2 := by
    rw [le_div_iff₀ hdenNear] at hnear
    nlinarith
  have hfar' : C * tail ≤ eps / 2 := by
    rw [le_div_iff₀ hdenFar] at hfar
    nlinarith
  exact annular_commutator_budget_below_epsilon C K beta tail eps
    hnear' hfar'

/-- The weak-`L^(3/2)` scale is exactly critical for amplitude `r^-2` on
volume `r^3`: cubing the quasi-norm removes fractional exponents. -/
theorem critical_blob_scale_identity
    (r : ℝ) (hr : r ≠ 0) :
    (1 / r ^ 2) ^ 3 * (r ^ 3) ^ 2 = 1 := by
  field_simp
  ring

/-- A velocity of size `r^-1` on volume `r^3` has squared `L^2` scale `r`. -/
theorem finite_energy_blob_scale_identity
    (r : ℝ) (hr : r ≠ 0) :
    (1 / r) ^ 2 * r ^ 3 = r := by
  field_simp
  ring

/-- Two scalar core values `0` and `1` cannot both be close to one common
mean. This is the finite shadow of the nonvanishing BMO oscillation. -/
theorem two_core_oscillation_floor (c : ℝ) :
    1 ≤ |c| + |1 - c| := by
  linarith [le_abs_self c, le_abs_self (1 - c)]

/-- If each of two incompatible cores occupies relative fraction `a`, their
contribution to mean oscillation is at least `a`. -/
theorem weighted_two_core_oscillation_floor
    (a c : ℝ) (ha : 0 ≤ a) :
    a ≤ a * |c| + a * |1 - c| := by
  have h := mul_le_mul_of_nonneg_left (two_core_oscillation_floor c) ha
  nlinarith

/-- Once the analytic lower coefficient strictly exceeds the complete upper
coefficient at the same positive scale, no energy value can satisfy both
bounds. -/
theorem amplification_upper_lower_contradiction
    (E scale lowerCoeff upperBase err : ℝ)
    (hscale : 0 < scale)
    (hcoeff : upperBase + err < lowerCoeff)
    (hupper : E ≤ (upperBase + err) * scale)
    (hlower : lowerCoeff * scale ≤ E) :
    False := by
  nlinarith

/-- Choosing the VMO error below the remaining coefficient margin preserves
the strict analytic contradiction. -/
theorem error_below_margin_closes_amplification
    (lowerCoeff upperBase err : ℝ)
    (hmargin : 0 < lowerCoeff - upperBase)
    (herr : err < lowerCoeff - upperBase) :
    upperBase + err < lowerCoeff := by
  linarith

#print axioms annular_commutator_budget_below_epsilon
#print axioms fixed_shell_rate_free_choice
#print axioms critical_blob_scale_identity
#print axioms finite_energy_blob_scale_identity
#print axioms two_core_oscillation_floor
#print axioms weighted_two_core_oscillation_floor
#print axioms amplification_upper_lower_contradiction
#print axioms error_below_margin_closes_amplification

end Round217NavierStokes
end Millennium
