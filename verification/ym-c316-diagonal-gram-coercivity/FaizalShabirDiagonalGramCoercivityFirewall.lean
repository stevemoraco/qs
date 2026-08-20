import Mathlib

/-!
# Faizal–Shabir diagonal-Gram coercivity firewall

Finite real algebra only.  This file formalizes two obstructions downstream of
C315's rooted-row theorem:

* the diagonal of a Gram matrix need not be controlled by the full Gram
  quadratic form (a rank-one Gram family has nontrivial coefficient null
  directions); and
* the naive ratio `|C_ij| / C_ii` is not invariant under rescaling one
  generator, whereas the squared normalized correlation coefficient is.

No Yang–Mills connected-correlation estimate, localized frame theorem, OS
Hilbert space, regulator/volume uniformity, mass gap, AF/IR theorem, or Clay
result is formalized here.
-/

namespace Millennium.YangMills.FaizalShabirDiagonalGramCoercivityFirewall

/-- Rank-one two-vector Gram form on the coefficient direction `(1,-1)` is
zero.  This is the scalar shadow of two identical physical Gram vectors. -/
theorem rank_one_gram_difference_is_zero :
    (1 : ℝ) - 1 - 1 + 1 = 0 := by
  norm_num

/-- The corresponding diagonal/local quadratic weight on `(1,-1)` is strictly
positive. -/
theorem diagonal_weight_survives_gram_null_direction :
    (1 : ℝ) * 1 ^ 2 + 1 * (-1) ^ 2 = 2 := by
  norm_num

/-- Consequently no finite scalar multiple of the rank-one Gram value `0` can
control the positive diagonal value `2`. -/
theorem no_finite_coercivity_on_rank_one_null_direction (K : ℝ) :
    ¬ ((2 : ℝ) ≤ K * 0) := by
  norm_num

/-- Under positive rescaling of the first generator, the naive off-diagonal to
first-diagonal ratio scales like `r / t`. -/
theorem naive_diagonal_ratio_under_rescaling
    (r t : ℝ) (ht : t ≠ 0) :
    (t * r) / (t ^ 2) = r / t := by
  field_simp

/-- The naive diagonal ratio can therefore exceed any prescribed nonnegative
bound by choosing a sufficiently small positive rescaling. -/
theorem naive_diagonal_ratio_can_be_arbitrarily_large
    (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M) :
    let t := r / (M + 1)
    0 < t ∧ r / t = M + 1 := by
  dsimp
  constructor
  · positivity
  · have hne : M + 1 ≠ 0 := by linarith
    field_simp

/-- In contrast, the squared normalized correlation coefficient is exactly
invariant under independent nonzero rescalings of both generators.  Squaring
avoids introducing square roots while retaining the scale-invariant content.
-/
theorem squared_normalized_correlation_is_rescaling_invariant
    (cij cii cjj ti tj : ℝ)
    (hti : ti ≠ 0) (htj : tj ≠ 0)
    (hcii : cii ≠ 0) (hcjj : cjj ≠ 0) :
    ((ti * tj * cij) ^ 2) /
        (((ti ^ 2) * cii) * ((tj ^ 2) * cjj)) =
      (cij ^ 2) / (cii * cjj) := by
  field_simp

/-- If a physical Gram form provides a positive lower Riesz/coercivity margin
`kappa * diagonal ≤ gram`, then a diagonal-relative harmful debt can be
converted into a physical-Gram-relative debt.  This is the exact additional
finite implication missing from the rank-one countermodel. -/
theorem diagonal_debt_to_physical_gram
    (debt diagonal gram eps kappa : ℝ)
    (hkappa : 0 < kappa)
    (hdebt : debt ≤ eps * diagonal)
    (hcoercive : kappa * diagonal ≤ gram)
    (heps : 0 ≤ eps) :
    debt ≤ (eps / kappa) * gram := by
  have hdiag : diagonal ≤ gram / kappa := by
    exact (le_div_iff₀ hkappa).2 (by simpa [mul_comm] using hcoercive)
  calc
    debt ≤ eps * diagonal := hdebt
    _ ≤ eps * (gram / kappa) :=
      mul_le_mul_of_nonneg_left hdiag heps
    _ = (eps / kappa) * gram := by
      field_simp

#print axioms rank_one_gram_difference_is_zero
#print axioms diagonal_weight_survives_gram_null_direction
#print axioms no_finite_coercivity_on_rank_one_null_direction
#print axioms naive_diagonal_ratio_under_rescaling
#print axioms naive_diagonal_ratio_can_be_arbitrarily_large
#print axioms squared_normalized_correlation_is_rescaling_invariant
#print axioms diagonal_debt_to_physical_gram

end Millennium.YangMills.FaizalShabirDiagonalGramCoercivityFirewall
