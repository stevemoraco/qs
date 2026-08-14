import Mathlib

/-!
# RG subleading-coefficient firewall

Finite scalar algebra for the dimensional-transmutation normalization gate.

For a weak-coupling RG step

    u' = u + b u^2 + c u^3,

the inverse coupling has the exact one-step drift

    1/u' - 1/u + b
      = u (b^2 + b c u - c) / (1 + b u + c u^2).

Hence the linear-in-u defect is governed by `b^2 - c`.  If one compensates
`1/(b u)` by a logarithmic term `p log u`, the first-order cancellation
condition is uniquely

    p = c / b^2 - 1,

so the corresponding coefficient of `log (1/u)` in a crossing-time asymptotic
is `1 - c / b^2`.

This file deliberately proves only the exact finite algebra.  It does not
formalize Taylor remainders, summability over RG steps, a Yang--Mills beta
function, scheme conversion, an interacting mass gap, or Osterwalder--Schrader
reconstruction.
-/

namespace Millennium.YangMills

/-- Cubic truncation of a weak-coupling scalar RG step. -/
def cubicRGStep (b c u : ℝ) : ℝ := u + b * u^2 + c * u^3

/-- Factorization used to expose the inverse-coupling drift. -/
theorem cubicRGStep_factor (b c u : ℝ) :
    cubicRGStep b c u = u * (1 + b * u + c * u^2) := by
  rw [cubicRGStep]
  ring

/-- Exact inverse-coupling defect for the cubic RG step. -/
theorem inverseCouplingDrift_exact
    {b c u : ℝ}
    (hu : u ≠ 0)
    (hden : 1 + b * u + c * u^2 ≠ 0) :
    1 / cubicRGStep b c u - 1 / u + b =
      u * (b^2 + b * c * u - c) / (1 + b * u + c * u^2) := by
  rw [cubicRGStep_factor]
  have hstep : u * (1 + b * u + c * u^2) ≠ 0 := mul_ne_zero hu hden
  field_simp [hu, hden, hstep]
  ring

/-- Coefficient multiplying `log u` that cancels the linear defect in the
standard compensated inverse-coupling potential. -/
def logCountertermCoeff (b c : ℝ) : ℝ := c / b^2 - 1

/-- The uncancelled linear drift for an arbitrary logarithmic coefficient `p`
is exactly `b` times the coefficient error. -/
theorem linearDriftResidual_exact
    {b c p : ℝ}
    (hb : b ≠ 0) :
    b - c / b + p * b = b * (p - logCountertermCoeff b c) := by
  rw [logCountertermCoeff]
  field_simp [hb]
  ring

/-- For nonzero leading beta coefficient, the logarithmic counterterm
coefficient is uniquely forced by first-order cancellation. -/
theorem logCountertermCoeff_unique
    {b c p : ℝ}
    (hb : b ≠ 0) :
    (b - c / b + p * b = 0) ↔ p = logCountertermCoeff b c := by
  rw [linearDriftResidual_exact hb]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hb0 | hp
    · exact (hb hb0).elim
    · exact sub_eq_zero.mp hp
  · intro hp
    rw [hp]
    ring

/-- The corresponding coefficient of `log (1/u)` has the opposite sign. -/
theorem crossingLogCoeff_eq
    {b c : ℝ} :
    -(logCountertermCoeff b c) = 1 - c / b^2 := by
  rw [logCountertermCoeff]
  ring

#print axioms cubicRGStep_factor
#print axioms inverseCouplingDrift_exact
#print axioms linearDriftResidual_exact
#print axioms logCountertermCoeff_unique
#print axioms crossingLogCoeff_eq

end Millennium.YangMills
