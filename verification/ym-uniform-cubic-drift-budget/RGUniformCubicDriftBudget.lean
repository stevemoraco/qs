import Mathlib

namespace Millennium.YangMills

/-- A uniform pointwise cubic-coefficient mismatch times a total coupling-sum
budget controls the weighted cubic drift. -/
theorem uniform_cubic_drift_weighted_budget
    (u delta : ℕ → ℝ) (N : ℕ)
    {D S W : ℝ}
    (hD : 0 ≤ D)
    (hu : ∀ n < N, 0 ≤ u n)
    (hdelta : ∀ n < N, |delta n| ≤ D)
    (hsum : (∑ n ∈ Finset.range N, u n) ≤ S)
    (hDS : D * S ≤ W) :
    (∑ n ∈ Finset.range N, |delta n| * u n) ≤ W := by
  have hpoint : ∀ n ∈ Finset.range N, |delta n| * u n ≤ D * u n := by
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    exact mul_le_mul_of_nonneg_right (hdelta n hnlt) (hu n hnlt)
  calc
    (∑ n ∈ Finset.range N, |delta n| * u n) ≤
        ∑ n ∈ Finset.range N, D * u n :=
      Finset.sum_le_sum hpoint
    _ = D * (∑ n ∈ Finset.range N, u n) := by
      rw [Finset.mul_sum]
    _ ≤ D * S :=
      mul_le_mul_of_nonneg_left hsum hD
    _ ≤ W := hDS

#print axioms uniform_cubic_drift_weighted_budget

end Millennium.YangMills
