import Mathlib

/-!
Finite scalar continuation of the weighted cubic-drift theorem.

If the per-step cubic coefficient mismatch is only linear in the weak coupling,
then the weighted clock error `|delta_n| * u_n` is quadratic in `u_n` and is
therefore paid by the same parabolic growth budget that pays the ordinary local
remainder.

This does not prove such a coefficient estimate for a Yang--Mills RG map.
-/

namespace Millennium.YangMills

/-- Linear decay of cubic-coefficient drift gives a uniform weighted drift
budget under the standard quadratic RG growth inequality. -/
theorem linear_cubic_drift_weighted_budget
    (u delta : ℕ → ℝ) (N : ℕ)
    {beta D : ℝ}
    (hbeta : 0 < beta)
    (hD : 0 ≤ D)
    (hu : ∀ n < N, 0 ≤ u n)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hdelta : ∀ n < N,
      |delta n| ≤ D * u n) :
    (∑ n in Finset.range N, |delta n| * u n) ≤
      (D / beta) * (u N - u 0) := by
  have hcoef : 0 ≤ D / beta :=
    div_nonneg hD (le_of_lt hbeta)
  have htel :
      (∑ n in Finset.range N, (u (n + 1) - u n)) = u N - u 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    (∑ n in Finset.range N, |delta n| * u n)
        ≤ ∑ n in Finset.range N, D * (u n)^2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hnlt : n < N := Finset.mem_range.mp hn
          have hun : 0 ≤ u n := hu n hnlt
          nlinarith [hdelta n hnlt]
    _ = ∑ n in Finset.range N,
        (D / beta) * (beta * (u n)^2) := by
          apply Finset.sum_congr rfl
          intro n hn
          field_simp [ne_of_gt hbeta]
    _ ≤ ∑ n in Finset.range N,
        (D / beta) * (u (n + 1) - u n) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnlt : n < N := Finset.mem_range.mp hn
          exact mul_le_mul_of_nonneg_left (hgrowth n hnlt) hcoef
    _ = (D / beta) * (u N - u 0) := by
          rw [← Finset.mul_sum, htel]

/-- If the weak trajectory remains in a fixed interval, linear cubic drift has
a regulator-independent total weighted budget. -/
theorem linear_cubic_drift_uniform_budget
    (u delta : ℕ → ℝ) (N : ℕ)
    {beta D U : ℝ}
    (hbeta : 0 < beta)
    (hD : 0 ≤ D)
    (hU : u N - u 0 ≤ U)
    (hu : ∀ n < N, 0 ≤ u n)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hdelta : ∀ n < N,
      |delta n| ≤ D * u n) :
    (∑ n in Finset.range N, |delta n| * u n) ≤
      (D / beta) * U := by
  calc
    (∑ n in Finset.range N, |delta n| * u n)
        ≤ (D / beta) * (u N - u 0) :=
          linear_cubic_drift_weighted_budget u delta N hbeta hD hu hgrowth hdelta
    _ ≤ (D / beta) * U := by
          exact mul_le_mul_of_nonneg_left hU
            (div_nonneg hD (le_of_lt hbeta))

#print axioms linear_cubic_drift_weighted_budget
#print axioms linear_cubic_drift_uniform_budget

end Millennium.YangMills
