import Mathlib

/-!
# Scalar core for a marginal cubic flow with an O(g^5) remainder

This file contains only finite real inequalities used by the Yang--Mills RG
audit. It encodes no gauge theory and makes no Millennium-problem claim.
-/

namespace YMProof
namespace MarginalRobustFinite

/-- An `O(g^5)` remainder perturbs the cubic fractional decrement by at most a
factor 3/2 in the explicit weak region. Here `e = r/g`. -/
theorem decrement_bounds
    (β C g e : ℝ)
    (hβ : 0 < β) (hC : 0 ≤ C)
    (he : |e| ≤ C * g^4)
    (hsmall : C * g^2 ≤ β / 2) :
    (β / 2) * g^2 ≤ β * g^2 - e ∧
      β * g^2 - e ≤ (3 * β / 2) * g^2 := by
  have hg2 : 0 ≤ g^2 := sq_nonneg g
  have hCg4 : C * g^4 ≤ (β / 2) * g^2 := by
    calc
      C * g^4 = (C * g^2) * g^2 := by ring
      _ ≤ (β / 2) * g^2 := mul_le_mul_of_nonneg_right hsmall hg2
  have he' := abs_le.mp he
  constructor <;> nlinarith

/-- Exact rational factor appearing in the reciprocal-square increment. -/
theorem rational_factor_bounds
    (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) :
    2 ≤ (2 - h) / (1 - h)^2 ∧
      (2 - h) / (1 - h)^2 ≤ 6 := by
  have hpos : 0 < 1 - h := by linarith
  have hden : 0 < (1 - h)^2 := sq_pos_of_pos hpos
  constructor
  · apply (le_div_iff₀ hden).2
    have haux : 0 ≤ h * (3 - 2 * h) := by
      apply mul_nonneg hh0
      linarith
    nlinarith
  · apply (div_le_iff₀ hden).2
    have h1 : 2 * h - 1 ≤ 0 := by linarith
    have h2 : 3 * h - 4 ≤ 0 := by linarith
    have haux : 0 ≤ (2 * h - 1) * (3 * h - 4) :=
      mul_nonneg_of_nonpos_of_nonpos h1 h2
    nlinarith

/-- Once the decrement-per-`g^2` lies in `[β/2,3β/2]` and the rational factor
lies in `[2,6]`, the reciprocal-square increment lies in `[β,9β]`. -/
theorem reciprocal_increment_product_bounds
    (β x y : ℝ)
    (hβ : 0 < β)
    (hxlo : β / 2 ≤ x) (hxhi : x ≤ 3 * β / 2)
    (hylo : 2 ≤ y) (hyhi : y ≤ 6) :
    β ≤ x * y ∧ x * y ≤ 9 * β := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  constructor
  · have hmul : (β / 2) * 2 ≤ x * y :=
      mul_le_mul hxlo hylo (by norm_num) hx0
    nlinarith
  · have hb0 : 0 ≤ 3 * β / 2 := by positivity
    have hmul : x * y ≤ (3 * β / 2) * 6 :=
      mul_le_mul hxhi hyhi hy0 hb0
    nlinarith

end MarginalRobustFinite
end YMProof
