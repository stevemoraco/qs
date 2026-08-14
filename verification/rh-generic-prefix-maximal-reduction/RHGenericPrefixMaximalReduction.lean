import Mathlib

/-!
# Generic normalized-prefix finite firewall

Finite real algebra only.

These declarations isolate the scalar inequalities behind a dyadic normalized
prefix-maximal argument and the weighted innovation square budget.  They do not
formalize orthogonal systems, integration, the Menchov--Rademacher inequality,
primes, prime gaps, published gap moments, Round239, zeta zeros, or RH.
-/

open scoped BigOperators

namespace RHGenericPrefixMaximalReduction

/-- The elementary square split used on every dyadic prefix block. -/
theorem square_add_le_two_squares (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- If `d ≤ n`, the dyadic denominator `d` safely majorizes the true prefix
normalization `n`. -/
theorem normalized_dyadic_split
    {a b d n : ℝ} (hd : 0 < d) (hdn : d ≤ n) :
    (a + b) ^ 2 / n ≤ 2 * (a ^ 2 + b ^ 2) / d := by
  have hn : 0 < n := hd.trans_le hdn
  have hq0 : 0 ≤ 2 * (a ^ 2 + b ^ 2) := by positivity
  have hqdiv0 : 0 ≤ 2 * (a ^ 2 + b ^ 2) / d :=
    div_nonneg hq0 hd.le
  apply (div_le_iff₀ hn).2
  calc
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) :=
      square_add_le_two_squares a b
    _ = (2 * (a ^ 2 + b ^ 2) / d) * d := by
      field_simp [ne_of_gt hd]
    _ ≤ (2 * (a ^ 2 + b ^ 2) / d) * n :=
      mul_le_mul_of_nonneg_left hdn hqdiv0

/-- The innovation coefficient pays only the gap square and logarithmic-center
square. -/
theorem innovation_square_le_two_parts (gap center : ℝ) :
    (gap - center) ^ 2 ≤ 2 * gap ^ 2 + 2 * center ^ 2 := by
  nlinarith [sq_nonneg (gap + center)]

/-- Nonnegative weights preserve the innovation square split after finite
summation. -/
theorem weighted_innovation_square_budget
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w gap center : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (gap i - center i) ^ 2) ≤
      ∑ i ∈ s, w i * (2 * gap i ^ 2 + 2 * center i ^ 2) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (innovation_square_le_two_parts (gap i) (center i)) (hw i hi)

/-- The arithmetic exponent produced by a cumulative square-gap bound is
strictly below the reported half-power target. -/
theorem one_third_strictly_below_one_half :
    (1 : ℚ) / 3 < 1 / 2 := by
  norm_num

/-- Raw smallness does not replace prefix normalization: an arbitrarily small
numerator can retain unit normalized square after a matching denominator. -/
theorem arbitrarily_small_raw_coefficient_unit_normalized_square
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a d : ℝ, 0 < a ∧ a < ε ∧ 0 < d ∧ a ^ 2 / d = 1 := by
  refine ⟨ε / 2, (ε / 2) ^ 2, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · positivity
  · field_simp [ne_of_gt hε]

#print axioms square_add_le_two_squares
#print axioms normalized_dyadic_split
#print axioms innovation_square_le_two_parts
#print axioms weighted_innovation_square_budget
#print axioms one_third_strictly_below_one_half
#print axioms arbitrarily_small_raw_coefficient_unit_normalized_square

end RHGenericPrefixMaximalReduction
