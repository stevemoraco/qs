import Mathlib

namespace Millennium.GaugeCore

noncomputable def fraction (x y : ℝ) : ℝ := y ^ 2 / (x ^ 2 + y ^ 2)

theorem firstAxis (x : ℝ) : fraction x 0 = 0 := by
  simp [fraction]

theorem secondAxis {y : ℝ} (hy : y ≠ 0) : fraction 0 y = 1 := by
  have hs : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  simp [fraction, hs]

theorem recurrenceBound
    (m d : ℕ → ℝ)
    (hstep : ∀ k, m (k + 1) ≥ m k - d k) :
    ∀ n, m n ≥ m 0 - ∑ k ∈ Finset.range n, d k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ]
      linarith

#print axioms firstAxis
#print axioms secondAxis
#print axioms recurrenceBound

end Millennium.GaugeCore
