import Mathlib

open BigOperators

namespace DyadicInversion

theorem finite_inversion
    (h m : ℕ → ℝ)
    (rec : ∀ k : ℕ,
      m (k + 1) = h k - 3 * h (k + 1) + 2 * h (k + 2)) :
    ∀ N : ℕ,
      h 0 =
        (∑ k in Finset.range N,
          (((2 : ℝ) ^ (k + 1) - 1) * m (k + 1)))
        + (((2 : ℝ) ^ (N + 1) - 1) * h N)
        - (((2 : ℝ) ^ (N + 1) - 2) * h (N + 1)) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, rec N]
      rw [ih]
      simp only [Nat.succ_eq_add_one, pow_succ]
      ring

#print axioms finite_inversion

end DyadicInversion
