import Mathlib

namespace BraidVerifier.RH

theorem finite_sequence_identity
    (h m : ℕ → ℝ)
    (step : ∀ k : ℕ,
      m (k + 1) = h k - 3 * h (k + 1) + 2 * h (k + 2)) :
    ∀ N : ℕ,
      h 0 =
        Finset.sum (Finset.range N)
          (fun k => (((2 : ℝ) ^ (k + 1) - 1) * m (k + 1)))
        + (((2 : ℝ) ^ (N + 1) - 1) * h N)
        - (((2 : ℝ) ^ (N + 1) - 2) * h (N + 1)) := by
  intro N
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, step N]
      rw [ih]
      simp only [pow_succ]
      ring

end BraidVerifier.RH
