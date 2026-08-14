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

For pure SU(N) Yang--Mills, inserting the universal one- and two-loop beta
coefficients gives the exact exponent

    b1 / (2 b0^2) = 51 / 121.

Thus a one-loop-only exponential scale `exp(-1/(2 b0 g^2))` misses the universal
power `(b0 g^2)^(-51/121)` appearing in the two-loop transmutation scale.

This file deliberately proves only exact finite algebra.  It does not formalize
Taylor remainders, summability over RG steps, scheme conversion, an interacting
mass gap, or Osterwalder--Schrader reconstruction.
-/

namespace Millennium.YangMills

/-- Cubic truncation of a weak-coupling scalar RG step. -/
def cubicRGStep (b c u : ℝ) : ℝ := u + b * u^2 + c * u^3

/-- Factorization used to expose the inverse-coupling drift. -/
theorem cubicRGStep_factor (b c u : ℝ) :
    cubicRGStep b c u = u * (1 + u * b + u^2 * c) := by
  rw [cubicRGStep]
  ring

/-- Exact inverse-coupling defect for the cubic RG step. -/
theorem inverseCouplingDrift_exact
    {b c u : ℝ}
    (hu : u ≠ 0)
    (hden : 1 + u * b + u^2 * c ≠ 0) :
    1 / cubicRGStep b c u - 1 / u + b =
      u * (b^2 + b * c * u - c) / (1 + u * b + u^2 * c) := by
  rw [cubicRGStep_factor]
  have hstep : u * (1 + u * b + u^2 * c) ≠ 0 := mul_ne_zero hu hden
  field_simp [hu, hden, hstep]
  ring

/-- Coefficient multiplying `log u` that cancels the linear defect in the
standard compensated inverse-coupling potential. -/
noncomputable def logCountertermCoeff (b c : ℝ) : ℝ := c / b^2 - 1

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

/-- Universal one-loop coefficient for pure SU(N), written with a real rank
parameter only to isolate the exact scalar cancellation. -/
noncomputable def pureSUBeta0 (N : ℝ) : ℝ :=
  11 * N / (48 * Real.pi^2)

/-- Universal two-loop coefficient for pure SU(N). -/
noncomputable def pureSUBeta1 (N : ℝ) : ℝ :=
  34 * N^2 / (3 * (16 * Real.pi^2)^2)

/-- For every nonzero rank parameter, the universal two-loop transmutation
exponent is exactly 51/121; all N and pi factors cancel. -/
theorem pureSU_twoLoopExponent
    {N : ℝ}
    (hN : N ≠ 0) :
    pureSUBeta1 N / (2 * (pureSUBeta0 N)^2) = (51 : ℝ) / 121 := by
  rw [pureSUBeta0, pureSUBeta1]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hN, hpi]
  ring

#print axioms cubicRGStep_factor
#print axioms inverseCouplingDrift_exact
#print axioms linearDriftResidual_exact
#print axioms logCountertermCoeff_unique
#print axioms crossingLogCoeff_eq
#print axioms pureSU_twoLoopExponent

end Millennium.YangMills
