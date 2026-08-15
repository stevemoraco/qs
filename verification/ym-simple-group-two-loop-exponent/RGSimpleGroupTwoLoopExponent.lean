import Mathlib

/-!
# Pure simple-group two-loop transmutation exponent

Finite scalar algebra for the Yang--Mills dimensional-transmutation denominator.
For a fixed compact simple gauge group, write `CA` for the adjoint quadratic
Casimir in the convention in which the standard pure-gauge coefficients are

    beta0 = 11 CA / (48 pi^2),
    beta1 = 34 CA^2 / (3 (16 pi^2)^2).

The ratio controlling the universal logarithmic correction to the transmutation
scale is independent of `CA`:

    beta1 / (2 beta0^2) = 51 / 121.

This extends the previously banked SU(N)-parameter algebra to the exact
fixed-simple-group variable appearing in Kirk v4.  The theorem is conditional
on the displayed standard beta-coefficient formulas; it does not prove those
physics inputs, scheme matching, finite-volume convergence, an interacting
spectral gap, Osterwalder--Schrader reconstruction, or the Clay theorem.
-/

namespace Millennium.YangMills

noncomputable def pureSimpleBeta0 (CA : ℝ) : ℝ :=
  11 * CA / (48 * Real.pi^2)

noncomputable def pureSimpleBeta1 (CA : ℝ) : ℝ :=
  34 * CA^2 / (3 * (16 * Real.pi^2)^2)

/-- The two-loop transmutation exponent is independent of the nonzero adjoint
Casimir parameter. -/
theorem pureSimple_twoLoopExponent
    {CA : ℝ}
    (hCA : CA ≠ 0) :
    pureSimpleBeta1 CA / (2 * (pureSimpleBeta0 CA)^2) = (51 : ℝ) / 121 := by
  rw [pureSimpleBeta0, pureSimpleBeta1]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hCA, hpi]
  ring

/-- Equivalent coefficient appearing in the physical logarithmic RG clock. -/
theorem pureSimple_physicalLogCoeff
    {CA : ℝ}
    (hCA : CA ≠ 0) :
    -(pureSimpleBeta1 CA / (2 * (pureSimpleBeta0 CA)^2)) = -(51 : ℝ) / 121 := by
  rw [pureSimple_twoLoopExponent hCA]

#print axioms pureSimple_twoLoopExponent
#print axioms pureSimple_physicalLogCoeff

end Millennium.YangMills
