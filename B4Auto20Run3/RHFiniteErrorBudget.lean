import Mathlib

open scoped BigOperators

namespace B4Auto20Run3

theorem rh_finite_error_strict_margin
    {ι : Type*} [Fintype ι]
    (m : ℝ) (e δ : ι → ℝ)
    (hbound : ∀ i, |e i| ≤ δ i)
    (hmargin : (∑ i, δ i) < m) :
    0 < m + ∑ i, e i := by
  have hlower : ∀ i, -δ i ≤ e i := by
    intro i
    exact (abs_le.mp (hbound i)).1
  have hsum : -(∑ i, δ i) ≤ ∑ i, e i := by
    calc
      -(∑ i, δ i) = ∑ i, -δ i := by simp
      _ ≤ ∑ i, e i := by
        exact Finset.sum_le_sum (fun i _ => hlower i)
  linarith

theorem rh_individual_error_bounds_do_not_aggregate :
    |(-3 / 4 : ℝ)| < 1 ∧
    |(-3 / 4 : ℝ)| < 1 ∧
    (1 : ℝ) + (-3 / 4) + (-3 / 4) < 0 := by
  norm_num [abs_of_nonpos]

#print axioms B4Auto20Run3.rh_finite_error_strict_margin
#print axioms B4Auto20Run3.rh_individual_error_bounds_do_not_aggregate

end B4Auto20Run3
