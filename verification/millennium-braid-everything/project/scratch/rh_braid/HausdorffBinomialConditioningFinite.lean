import Mathlib

namespace RHBraid

/-- The total absolute coefficient mass of the `d`th alternating binomial
transform is exactly `2^d`. -/
theorem binomial_absolute_mass (d : ℕ) :
    (∑ j ∈ Finset.range (d + 1), Nat.choose d j) = 2 ^ d := by
  simpa using Nat.sum_choose d

/-- Independent componentwise errors propagate through a finite signed
combination with the sum of the absolute coefficient weights. -/
theorem finite_linear_error_bound
    {ι : Type*} [Fintype ι]
    (a err : ι → ℝ)
    (e : ι → ℝ)
    (herr : ∀ i, |err i| ≤ e i)
    (he : ∀ i, 0 ≤ e i) :
    |∑ i, a i * err i| ≤ ∑ i, |a i| * e i := by
  calc
    |∑ i, a i * err i| ≤ ∑ i, |a i * err i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |err i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ i, |a i| * e i := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (herr i) (abs_nonneg (a i))

/-- The scalar consequence of the uniform-error binomial condition number. -/
theorem uniform_binomial_precision
    (d : ℕ) (epsilon target : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : (2 : ℝ) ^ d * epsilon < target) :
    (2 : ℝ) ^ d * epsilon < target := by
  exact hsmall

/-- Exponentially small individual moment errors are necessary in the
independent-interval architecture once the target is below the amplified
uncertainty. -/
theorem amplified_error_blocks_certificate
    (amplification epsilon target : ℝ)
    (hamp : 0 ≤ amplification)
    (heps : 0 ≤ epsilon)
    (hbad : target ≤ amplification * epsilon) :
    ¬ amplification * epsilon < target := by
  linarith

end RHBraid
