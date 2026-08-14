import Mathlib

namespace RHCubicPrimeGapDebtFinite

/-- A finite cubic moment is bounded by a uniform first-moment ceiling times
the corresponding quadratic moment. This is the exact finite inequality used
on each dyadic prime block. -/
theorem cube_sum_le_max_mul_square
    {ι : Type*} (s : Finset ι) (g : ι → ℝ) (M S : ℝ)
    (hM0 : 0 ≤ M)
    (hgM : ∀ i ∈ s, g i ≤ M)
    (hS : ∑ i ∈ s, (g i) ^ 2 ≤ S) :
    ∑ i ∈ s, (g i) ^ 3 ≤ M * S := by
  calc
    ∑ i ∈ s, (g i) ^ 3 ≤ ∑ i ∈ s, M * (g i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hsquare : 0 ≤ (g i) ^ 2 := sq_nonneg (g i)
      nlinarith [hgM i hi]
    _ = M * (∑ i ∈ s, (g i) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ M * S := mul_le_mul_of_nonneg_left hS hM0

/-- The exact exponent left by Ingham's `5/8` gap bound and Heath-Brown's
`4/3` quadratic-moment bound after the denominator contributes `-2`. -/
theorem classical_dyadic_exponent :
    (-2 : ℚ) + 5 / 8 + 4 / 3 = -1 / 24 := by
  norm_num

/-- The fixed epsilon `1/100` leaves a strict negative dyadic exponent. -/
theorem fixed_epsilon_margin :
    (-1 / 24 : ℚ) + 1 / 100 = -19 / 600 ∧
    (-19 / 600 : ℚ) < 0 := by
  norm_num

/-- Abstract comparison terminal: a nonnegative block sequence dominated by a
summable nonnegative majorant is summable. -/
theorem summable_of_summable_block_majorant
    (block majorant : ℕ → ℝ)
    (hblock : ∀ n, 0 ≤ block n)
    (hle : ∀ n, block n ≤ majorant n)
    (hmajorant : Summable majorant) :
    Summable block := by
  exact Summable.of_nonneg_of_le hblock hle hmajorant

/-- Once a cumulative nonnegative debt is bounded above by a finite total,
every partial debt is uniformly bounded. -/
theorem partial_debt_bounded
    (partialDebt : ℕ → ℝ) (total : ℝ)
    (h : ∀ N, partialDebt N ≤ total) :
    ∀ N, partialDebt N ≤ total := h

/-- A bounded nonnegative debt is automatically subpower at the elementary
comparison level: every positive power threshold above the bound dominates it. -/
theorem bounded_debt_below_positive_power
    (debt X epsilon C : ℝ)
    (hdebt : debt ≤ C)
    (hpower : C ≤ X ^ epsilon) :
    debt ≤ X ^ epsilon := by
  exact hdebt.trans hpower

#print axioms RHCubicPrimeGapDebtFinite.cube_sum_le_max_mul_square
#print axioms RHCubicPrimeGapDebtFinite.classical_dyadic_exponent
#print axioms RHCubicPrimeGapDebtFinite.fixed_epsilon_margin
#print axioms RHCubicPrimeGapDebtFinite.summable_of_summable_block_majorant
#print axioms RHCubicPrimeGapDebtFinite.partial_debt_bounded
#print axioms RHCubicPrimeGapDebtFinite.bounded_debt_below_positive_power

end RHCubicPrimeGapDebtFinite
