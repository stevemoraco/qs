import Mathlib

/-!
# Reflected-beta AO finite coefficient obstruction

This file formalizes only the exact rational polynomial calculation banked in
`stevemoraco/RH#300`.  At the dimensionless Gaussian critical coordinate
`z = a*y^2 = 1/2`, the stripped phase-derivative factor vanishes, while the
restored stripped derivative of the leading `b` profile is `-8` and hence does
not vanish.  The selected reflected ratio is also nonresonant and distinct
from the parent ratio.

Nothing here formalizes Gaussian differentiation, the Albritton--Ozański
source asymptotics, remainder estimates, a glued eigenfunction, any PDE, or a
Clay Millennium theorem.
-/

namespace NSAOReflectedBetaFinite

def z : ℚ := 1 / 2
def betaZero : ℚ := 1
def betaOne : ℚ := -1 / 2
def radiusZero : ℚ := 1

/-- The positive exponential and nonzero scalar prefactors have been removed
from the leading phase derivative `w_y`. -/
def phaseDerivativeFactor : ℚ := 1 - 2 * z

/-- The positive exponential and nonzero scalar prefactors have been removed
from `w * w_yy`. -/
def bDerivativeReducedFactor : ℚ := z * (-6 + 4 * z)

/-- Restore the rational numerical prefactor `4` (but not the positive
Gaussian/scalar factors). -/
def bDerivativeRestoredFactor : ℚ := 4 * bDerivativeReducedFactor

/-- Fixed-parameter coefficient in the leading `H_betaOne` profile. -/
def nonresonanceFactor : ℚ :=
  1 + betaOne * betaZero * radiusZero ^ 2

/-- Difference between the reflected candidate ratio and parent ratio. -/
def phaseDifference : ℚ := betaOne - betaZero

/-- Finite coefficient-level simultaneous leading criticality means that both
stripped derivative factors vanish at the selected coordinate. -/
def SimultaneousLeadingCriticality : Prop :=
  phaseDerivativeFactor = 0 ∧ bDerivativeRestoredFactor = 0

/-- The selected coordinate is a critical point of the stripped leading phase
profile. -/
theorem phaseDerivativeFactorValue : phaseDerivativeFactor = 0 := by
  norm_num [phaseDerivativeFactor, z]

/-- The reduced rational factor in `w * w_yy` is exactly `-2`. -/
theorem bDerivativeReducedFactorValue : bDerivativeReducedFactor = -2 := by
  norm_num [bDerivativeReducedFactor, z]

/-- Restoring the rational prefactor gives the exact factor `-8`. -/
theorem bDerivativeRestoredFactorValue :
    bDerivativeRestoredFactor = -8 := by
  norm_num [bDerivativeRestoredFactor, bDerivativeReducedFactor, z]

/-- Therefore the stripped leading `b`-derivative coefficient is nonzero. -/
theorem bDerivativeRestoredFactorNonzero :
    bDerivativeRestoredFactor ≠ 0 := by
  rw [bDerivativeRestoredFactorValue]
  norm_num

/-- The chosen reflected parameters are away from the singular algebraic
resonance: `1 + betaOne * betaZero * radiusZero^2 = 1/2`. -/
theorem nonresonanceFactorValue : nonresonanceFactor = 1 / 2 := by
  norm_num [nonresonanceFactor, betaOne, betaZero, radiusZero]

theorem nonresonanceFactorNonzero : nonresonanceFactor ≠ 0 := by
  rw [nonresonanceFactorValue]
  norm_num

/-- The reflected and parent ratios differ by `-3/2`. -/
theorem phaseDifferenceValue : phaseDifference = -3 / 2 := by
  norm_num [phaseDifference, betaOne, betaZero]

theorem phaseDifferenceNonzero : phaseDifference ≠ 0 := by
  rw [phaseDifferenceValue]
  norm_num

/-- Exact finite conclusion: the phase critical coefficient and the leading
`b`-derivative coefficient cannot vanish simultaneously at this witness. -/
theorem noSimultaneousLeadingCriticality :
    ¬ SimultaneousLeadingCriticality := by
  intro h
  exact bDerivativeRestoredFactorNonzero h.2

/-- One bundled certificate recording every rational value used by the finite
countercalculation. -/
theorem finiteCoefficientCertificate :
    phaseDerivativeFactor = 0 ∧
      bDerivativeReducedFactor = -2 ∧
      bDerivativeRestoredFactor = -8 ∧
      nonresonanceFactor = 1 / 2 ∧
      phaseDifference = -3 / 2 := by
  exact ⟨phaseDerivativeFactorValue,
    bDerivativeReducedFactorValue,
    bDerivativeRestoredFactorValue,
    nonresonanceFactorValue,
    phaseDifferenceValue⟩

#print axioms phaseDerivativeFactorValue
#print axioms bDerivativeReducedFactorValue
#print axioms bDerivativeRestoredFactorValue
#print axioms bDerivativeRestoredFactorNonzero
#print axioms nonresonanceFactorValue
#print axioms nonresonanceFactorNonzero
#print axioms phaseDifferenceValue
#print axioms phaseDifferenceNonzero
#print axioms noSimultaneousLeadingCriticality
#print axioms finiteCoefficientCertificate

end NSAOReflectedBetaFinite
