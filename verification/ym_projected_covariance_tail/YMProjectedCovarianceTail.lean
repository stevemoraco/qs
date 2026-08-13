import Mathlib

namespace YMProjectedCovarianceTail

theorem linear_square_error_of_two_sided_bound
    (m mK K δm : ℝ)
    (hm : |m| ≤ K)
    (hmK : |mK| ≤ K)
    (herr : |m - mK| ≤ δm) :
    |m ^ 2 - mK ^ 2| ≤ 2 * K * δm := by
  have hsum : |m + mK| ≤ 2 * K := by
    calc
      |m + mK| ≤ |m| + |mK| := abs_add m mK
      _ ≤ K + K := add_le_add hm hmK
      _ = 2 * K := by ring
  have hδm : 0 ≤ δm := le_trans (abs_nonneg (m - mK)) herr
  calc
    |m ^ 2 - mK ^ 2| =
        |m - mK| * |m + mK| := by
          rw [show m ^ 2 - mK ^ 2 = (m - mK) * (m + mK) by ring, abs_mul]
    _ ≤ δm * (2 * K) :=
      mul_le_mul herr hsum (abs_nonneg (m + mK)) hδm
    _ = 2 * K * δm := by ring

theorem linear_projected_mass_error_of_two_sided_bound
    (A AK m mK δG δm K : ℝ)
    (hA : |A - AK| ≤ δG)
    (hm : |m| ≤ K)
    (hmK : |mK| ≤ K)
    (hmerr : |m - mK| ≤ δm) :
    |(A - m ^ 2) - (AK - mK ^ 2)| ≤ δG + 2 * K * δm := by
  have hsquare :=
    linear_square_error_of_two_sided_bound m mK K δm hm hmK hmerr
  calc
    |(A - m ^ 2) - (AK - mK ^ 2)| =
        |(A - AK) - (m ^ 2 - mK ^ 2)| := by
          congr 1
          ring
    _ ≤ |A - AK| + |m ^ 2 - mK ^ 2| :=
      abs_sub (A - AK) (m ^ 2 - mK ^ 2)
    _ ≤ δG + 2 * K * δm := add_le_add hA hsquare

theorem quadratic_square_error_of_one_sided_bound
    (m mK K δm : ℝ)
    (hm : |m| ≤ K)
    (herr : |m - mK| ≤ δm) :
    |m ^ 2 - mK ^ 2| ≤ δm * (2 * K + δm) := by
  have hmK : |mK| ≤ K + δm := by
    calc
      |mK| = |m - (m - mK)| := by
        congr 1
        ring
      _ ≤ |m| + |m - mK| := abs_sub m (m - mK)
      _ ≤ K + δm := add_le_add hm herr
  have hsum : |m + mK| ≤ 2 * K + δm := by
    calc
      |m + mK| ≤ |m| + |mK| := abs_add m mK
      _ ≤ K + (K + δm) := add_le_add hm hmK
      _ = 2 * K + δm := by ring
  have hδm : 0 ≤ δm := le_trans (abs_nonneg (m - mK)) herr
  calc
    |m ^ 2 - mK ^ 2| =
        |m - mK| * |m + mK| := by
          rw [show m ^ 2 - mK ^ 2 = (m - mK) * (m + mK) by ring, abs_mul]
    _ ≤ δm * (2 * K + δm) :=
      mul_le_mul herr hsum (abs_nonneg (m + mK)) hδm

theorem quadratic_projected_mass_error_of_one_sided_bound
    (A AK m mK δG δm K : ℝ)
    (hA : |A - AK| ≤ δG)
    (hm : |m| ≤ K)
    (hmerr : |m - mK| ≤ δm) :
    |(A - m ^ 2) - (AK - mK ^ 2)| ≤
      δG + δm * (2 * K + δm) := by
  have hsquare :=
    quadratic_square_error_of_one_sided_bound m mK K δm hm hmerr
  calc
    |(A - m ^ 2) - (AK - mK ^ 2)| =
        |(A - AK) - (m ^ 2 - mK ^ 2)| := by
          congr 1
          ring
    _ ≤ |A - AK| + |m ^ 2 - mK ^ 2| :=
      abs_sub (A - AK) (m ^ 2 - mK ^ 2)
    _ ≤ δG + δm * (2 * K + δm) := add_le_add hA hsquare

theorem projected_trace_tail_lower
    {M : ℕ}
    (A AK m mK : Fin M → ℝ)
    (δG δm K : ℝ)
    (hA : ∀ i, |A i - AK i| ≤ δG)
    (hm : ∀ i, |m i| ≤ K)
    (hmK : ∀ i, |mK i| ≤ K)
    (hmerr : ∀ i, |m i - mK i| ≤ δm) :
    (∑ i, (AK i - (mK i) ^ 2)) -
        (M : ℝ) * (δG + 2 * K * δm) ≤
      ∑ i, (A i - (m i) ^ 2) := by
  have hpoint :
      ∀ i, (AK i - (mK i) ^ 2) - (δG + 2 * K * δm) ≤
        A i - (m i) ^ 2 := by
    intro i
    have h :=
      (abs_le.mp
        (linear_projected_mass_error_of_two_sided_bound
          (A i) (AK i) (m i) (mK i) δG δm K
          (hA i) (hm i) (hmK i) (hmerr i))).1
    linarith
  have hsum :
      (∑ i, ((AK i - (mK i) ^ 2) - (δG + 2 * K * δm))) ≤
        ∑ i, (A i - (m i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  simpa [Finset.sum_sub_distrib] using hsum

theorem one_sided_linear_bound_counterexample :
    |(0 : ℝ)| ≤ 0 ∧
    |(0 : ℝ) - 1| ≤ 1 ∧
    ¬ (|(0 : ℝ) ^ 2 - 1 ^ 2| ≤ 2 * 0 * 1) := by
  norm_num

#print axioms linear_square_error_of_two_sided_bound
#print axioms linear_projected_mass_error_of_two_sided_bound
#print axioms quadratic_square_error_of_one_sided_bound
#print axioms quadratic_projected_mass_error_of_one_sided_bound
#print axioms projected_trace_tail_lower
#print axioms one_sided_linear_bound_counterexample

end YMProjectedCovarianceTail
