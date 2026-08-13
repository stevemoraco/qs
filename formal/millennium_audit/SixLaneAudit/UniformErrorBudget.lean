import Mathlib

namespace SixLaneAudit.UniformErrorBudget

/-- A strict absolute-error bound by half of a reference value gives a strict
half-reference lower bound. -/
theorem tail_lower_of_abs_error
    {q : ℕ → ℝ} {N : ℕ} {M : ℝ}
    (htail : ∀ n, N ≤ n → |q n - M| < M / 2) :
    ∀ n, N ≤ n → M / 2 < q n := by
  intro n hn
  have hlower := (abs_lt.mp (htail n hn)).1
  linarith

/-- Indexed half-gap gate: one strict error budget controls every tail index. -/
theorem tail_half_gap_of_error_budget
    {q : ℕ → ℝ} {N : ℕ} {M eps : ℝ}
    (hbudget : eps < M / 2)
    (herr : ∀ n, N ≤ n → |q n - M| ≤ eps) :
    ∀ n, N ≤ n → M / 2 < q n := by
  apply tail_lower_of_abs_error
  intro n hn
  exact lt_of_le_of_lt (herr n hn) hbudget

/-- Finite exceptional checks plus a uniform tail approximation yield one
positive lower bound valid at every index. -/
theorem finite_prefix_error_budget_uniform_margin
    {q : ℕ → ℝ} {N : ℕ} {delta M eps : ℝ}
    (hdelta : 0 < delta)
    (hM : 0 < M)
    (hbudget : eps < M / 2)
    (hprefix : ∀ n, n < N → delta ≤ q n)
    (herr : ∀ n, N ≤ n → |q n - M| ≤ eps) :
    0 < min delta (M / 2) ∧
      ∀ n, min delta (M / 2) ≤ q n := by
  constructor
  · have hhalf : 0 < M / 2 := by linarith
    exact lt_min hdelta hhalf
  · intro n
    by_cases hn : n < N
    · exact le_trans (min_le_left _ _) (hprefix n hn)
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      have htail : M / 2 < q n :=
        tail_half_gap_of_error_budget hbudget herr n hn'
      exact le_trans (min_le_right _ _) (le_of_lt htail)

/-- Sharpness obstruction: weakening the strict budget to `eps ≤ M/2` allows
the boundary case `q = M/2`, so the strict half-gap conclusion can fail. -/
theorem nonstrict_budget_allows_boundary :
    ∃ (M eps q : ℝ),
      0 < M ∧
      eps ≤ M / 2 ∧
      |q - M| ≤ eps ∧
      ¬ (M / 2 < q) := by
  refine ⟨2, 1, 1, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms tail_lower_of_abs_error
#print axioms tail_half_gap_of_error_budget
#print axioms finite_prefix_error_budget_uniform_margin
#print axioms nonstrict_budget_allows_boundary

end SixLaneAudit.UniformErrorBudget
