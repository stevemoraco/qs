import Mathlib

/-!
# Navier--Stokes projected-to-raw dilation firewall

This file formalizes only the scalar finite model showing that tangent
stationarity and an invertible one-dimensional constraint Gram matrix do not
imply raw-dilation stationarity. It does not formalize Ekeland's principle,
constraint manifolds, Pohozaev identities, or Navier--Stokes.
-/

namespace MillenniumBraid
namespace B2Round42NSProjection

/-- Value data at the unique constrained point. -/
def transferValue : ℝ := 1

def visibilityValue : ℝ := 1

def quotientValue : ℝ := 1

/-- Raw-dilation derivative data with the source's homogeneities. -/
def transferRawDerivative : ℝ := (3 : ℝ) / 2

def visibilityRawDerivative : ℝ := 2

/-- The projected tangent space of the singleton constraint is zero. -/
def projectedDerivative : ℝ := 0

/-- The near-maximizing value identity holds exactly. -/
theorem value_identity :
    transferValue = quotientValue * visibilityValue := by
  norm_num [transferValue, quotientValue, visibilityValue]

/-- The transfer raw derivative has degree `3/2`. -/
theorem transfer_raw_homogeneity :
    transferRawDerivative = (3 : ℝ) / 2 * transferValue := by
  norm_num [transferRawDerivative, transferValue]

/-- The visibility raw derivative has degree two. -/
theorem visibility_raw_homogeneity :
    visibilityRawDerivative = 2 * visibilityValue := by
  norm_num [visibilityRawDerivative, visibilityValue]

/-- Every derivative on the zero tangent space vanishes. -/
theorem tangent_stationarity : projectedDerivative = 0 := by
  rfl

/-- The raw derivative of `T - Lambda*V` is exactly `-1/2`. -/
theorem raw_multiplier_contribution :
    transferRawDerivative - quotientValue * visibilityRawDerivative
      = -(1 : ℝ) / 2 := by
  norm_num [transferRawDerivative, quotientValue, visibilityRawDerivative]

/-- The raw derivative is not equal to the projected tangent derivative. -/
theorem projected_to_raw_identity_fails :
    transferRawDerivative - quotientValue * visibilityRawDerivative
      ≠ projectedDerivative := by
  norm_num [transferRawDerivative, quotientValue, visibilityRawDerivative,
    projectedDerivative]

/-- Scalar Gram matrix of the singleton constraint is uniformly invertible. -/
theorem scalar_constraint_gram_positive : (0 : ℝ) < 1 := by
  norm_num

/-- Packing all finite facts: exact value identity, tangent stationarity,
positive Gram scalar, and nonzero raw normal derivative coexist. -/
theorem constrained_stationarity_does_not_force_raw_stationarity :
    transferValue = quotientValue * visibilityValue ∧
    projectedDerivative = 0 ∧
    (0 : ℝ) < 1 ∧
    transferRawDerivative - quotientValue * visibilityRawDerivative
      ≠ projectedDerivative := by
  exact ⟨value_identity, tangent_stationarity, scalar_constraint_gram_positive,
    projected_to_raw_identity_fails⟩

#print axioms value_identity
#print axioms transfer_raw_homogeneity
#print axioms visibility_raw_homogeneity
#print axioms tangent_stationarity
#print axioms raw_multiplier_contribution
#print axioms projected_to_raw_identity_fails
#print axioms scalar_constraint_gram_positive
#print axioms constrained_stationarity_does_not_force_raw_stationarity

end B2Round42NSProjection
end MillenniumBraid
