import Mathlib

open BigOperators

namespace MillenniumBraidUnified

namespace RHCore

theorem dyadic_formula
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

end RHCore

namespace PNPCore

theorem pow_lt_pow_succ (N k : ℕ) (hN : 2 ≤ N) :
    N ^ k < N ^ (k + 1) := by
  rw [Nat.pow_succ]
  have hpos : 0 < N ^ k := Nat.pow_pos (by omega)
  have htwo : 2 * (N ^ k) ≤ N * (N ^ k) := by
    exact Nat.mul_le_mul_right (N ^ k) hN
  have hlt : N ^ k < 2 * (N ^ k) := by
    omega
  omega

theorem no_fixed_exponent_dominates_all_polynomial_exponents (k : ℕ) :
    ∃ i : ℕ, k < i ∧ ∀ N : ℕ, 2 ≤ N → N ^ k < N ^ i := by
  refine ⟨k + 1, Nat.lt_succ_self k, ?_⟩
  intro N hN
  exact pow_lt_pow_succ N k hN

end PNPCore

end MillenniumBraidUnified
