import Mathlib

/-!
# Common-mode covariance capture firewall

Finite scalar core for the exact common-mode obstruction to covariance capture.
A normalized block average of `N` inputs of the form

`X_i = shared + private_i`

has squared selected-coordinate/block-average correlation

`rho² = (N * sharedVar + privateVar) / (N * (sharedVar + privateVar))`.

The corresponding product-capacity and matched-rate inequalities reduce to
explicit shared/private variance budgets.  The operator-valued Gaussian theorem,
covariance square roots, canonical correlations, polymer RG, gauge fields,
Yang--Mills, a mass gap, and every Clay endpoint remain external.
-/

namespace Millennium.YangMills.CommonModeCaptureFirewall

/-- Squared scalar canonical correlation for one selected coordinate and the
normalized block average in the shared-plus-private Gaussian model. -/
noncomputable def rhoSq (N sharedVar privateVar : ℝ) : ℝ :=
  (N * sharedVar + privateVar) / (N * (sharedVar + privateVar))

/-- The normalized covariance capture is the complement of squared
correlation. -/
noncomputable def capture (N sharedVar privateVar : ℝ) : ℝ :=
  1 - rhoSq N sharedVar privateVar

/-- Exact capture formula. -/
theorem capture_eq
    (N sharedVar privateVar : ℝ)
    (hN : N ≠ 0) (hsum : sharedVar + privateVar ≠ 0) :
    capture N sharedVar privateVar =
      ((N - 1) * privateVar) / (N * (sharedVar + privateVar)) := by
  unfold capture rhoSq
  field_simp [hN, hsum]
  ring

/-- Denominator-cleared product-capacity debt. -/
theorem productDebt_identity
    (N r sharedVar privateVar : ℝ) :
    r * (N * sharedVar + privateVar) - N * (sharedVar + privateVar) =
      N * (r - 1) * sharedVar - (N - r) * privateVar := by
  ring

/-- The strict all-functions product margin is exactly a shared/private
variance budget after denominators are cleared. -/
theorem productMargin_iff_commonModeBudget
    (N r sharedVar privateVar : ℝ) :
    r * (N * sharedVar + privateVar) < N * (sharedVar + privateVar) ↔
      N * (r - 1) * sharedVar < (N - r) * privateVar := by
  have hident := productDebt_identity N r sharedVar privateVar
  constructor <;> intro h <;> nlinarith

/-- Denominator-cleared matched-rate debt for a target squared contraction
`1 / b²`. -/
theorem matchedDebt_identity
    (N b sharedVar privateVar : ℝ) :
    b ^ 2 * (N * sharedVar + privateVar) -
        N * (sharedVar + privateVar) =
      N * (b ^ 2 - 1) * sharedVar -
        (N - b ^ 2) * privateVar := by
  ring

/-- At four-dimensional block multiplicity `N=b⁴`, the matched-rate debt
factors through the single scalar ticket `b² * sharedVar - privateVar`. -/
theorem fourDimensionalMatchedDebt_factor
    (b sharedVar privateVar : ℝ) :
    b ^ 2 * (b ^ 4 * sharedVar + privateVar) -
        b ^ 4 * (sharedVar + privateVar) =
      b ^ 2 * (b ^ 2 - 1) * (b ^ 2 * sharedVar - privateVar) := by
  ring

/-- Dyadic four-dimensional specialization: squared contraction at most `1/4`
is equivalent to the exact common-mode ticket `4 * sharedVar ≤ privateVar`. -/
theorem dyadicFourDimensionalMatched_iff
    (sharedVar privateVar : ℝ) :
    4 * (16 * sharedVar + privateVar) ≤
        16 * (sharedVar + privateVar) ↔
      4 * sharedVar ≤ privateVar := by
  constructor <;> intro h <;> nlinarith

/-- If the shared mode is retained/conditioned away, the scalar squared
correlation is exactly `1/N`. -/
theorem privateOnly_rhoSq
    (N privateVar : ℝ) (hN : N ≠ 0) (hprivate : privateVar ≠ 0) :
    rhoSq N 0 privateVar = 1 / N := by
  unfold rhoSq
  field_simp [hN, hprivate]
  ring

/-- Exact dyadic common-mode witness: equal shared and private variances give
squared correlation `17/32`, far above the matched target `1/4`. -/
theorem dyadicEqualSharedPrivate_rhoSq
    (v : ℝ) (hv : v ≠ 0) :
    rhoSq 16 v v = 17 / 32 := by
  unfold rhoSq
  field_simp [hv]
  ring

/-- The same witness violates the four-factor product condition by the exact
factor `17/8`. -/
theorem dyadicEqualSharedPrivate_fourFactor
    (v : ℝ) (hv : v ≠ 0) :
    4 * rhoSq 16 v v = 17 / 8 := by
  rw [dyadicEqualSharedPrivate_rhoSq v hv]
  ring

/-- In particular the equal shared/private dyadic witness has product debt
strictly above one. -/
theorem dyadicEqualSharedPrivate_noFourFactorMargin
    (v : ℝ) (hv : v ≠ 0) :
    1 < 4 * rhoSq 16 v v := by
  rw [dyadicEqualSharedPrivate_fourFactor v hv]
  norm_num

#print axioms capture_eq
#print axioms productDebt_identity
#print axioms productMargin_iff_commonModeBudget
#print axioms matchedDebt_identity
#print axioms fourDimensionalMatchedDebt_factor
#print axioms dyadicFourDimensionalMatched_iff
#print axioms privateOnly_rhoSq
#print axioms dyadicEqualSharedPrivate_rhoSq
#print axioms dyadicEqualSharedPrivate_fourFactor
#print axioms dyadicEqualSharedPrivate_noFourFactorMargin

end Millennium.YangMills.CommonModeCaptureFirewall
