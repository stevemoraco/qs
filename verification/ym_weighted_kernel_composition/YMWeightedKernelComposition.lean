import Mathlib

open scoped BigOperators

namespace YMWeightedKernelComposition

/-- Finite weighted row-bound composition lemma. -/
theorem weighted_row_comp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B w : ι → ι → ℝ)
    (KA KB : ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j)
    (hw : ∀ i j k, w i k ≤ w i j * w j k)
    (hw0 : ∀ i j, 0 ≤ w i j)
    (hKB : 0 ≤ KB)
    (hrowA : ∀ i, (∑ j, w i j * A i j) ≤ KA)
    (hrowB : ∀ j, (∑ k, w j k * B j k) ≤ KB) :
    ∀ i, (∑ k, w i k * (∑ j, A i j * B j k)) ≤ KA * KB := by
  intro i
  calc
    (∑ k, w i k * (∑ j, A i j * B j k)) =
        ∑ k, ∑ j, w i k * (A i j * B j k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
    _ = ∑ j, ∑ k, w i k * (A i j * B j k) := by
          rw [Finset.sum_comm]
    _ ≤ ∑ j, ∑ k, (w i j * w j k) * (A i j * B j k) := by
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right (hw i j k)
            (mul_nonneg (hA i j) (hB j k))
    _ = ∑ j, (w i j * A i j) * (∑ k, w j k * B j k) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ ≤ ∑ j, (w i j * A i j) * KB := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hrowB j)
            (mul_nonneg (hw0 i j) (hA i j))
    _ = (∑ j, w i j * A i j) * KB := by
          rw [Finset.sum_mul]
    _ ≤ KA * KB := by
          exact mul_le_mul_of_nonneg_right (hrowA i) hKB

/-- Equal row bounds square under one composition. -/
theorem weighted_row_comp_same
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B w : ι → ι → ℝ)
    (K : ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hB : ∀ i j, 0 ≤ B i j)
    (hw : ∀ i j k, w i k ≤ w i j * w j k)
    (hw0 : ∀ i j, 0 ≤ w i j)
    (hK : 0 ≤ K)
    (hrowA : ∀ i, (∑ j, w i j * A i j) ≤ K)
    (hrowB : ∀ j, (∑ k, w j k * B j k) ≤ K) :
    ∀ i, (∑ k, w i k * (∑ j, A i j * B j k)) ≤ K ^ 2 := by
  intro i
  have h := weighted_row_comp A B w K K hA hB hw hw0 hK hrowA hrowB i
  simpa [pow_two] using h

#print axioms weighted_row_comp
#print axioms weighted_row_comp_same

end YMWeightedKernelComposition
