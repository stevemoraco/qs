import Mathlib

namespace YangMillsBraid

/-- Every finite cutoff eigenvalue in the model lies strictly below one. -/
theorem cutoff_eigenvalue_strict (N : ℕ) :
    (1 : ℝ) - 1 / (N + 1 : ℝ) < 1 := by
  have hpos : 0 < (N + 1 : ℝ) := by positivity
  have : 0 < 1 / (N + 1 : ℝ) := one_div_pos.mpr hpos
  linarith

/-- The cutoff eigenvalues approach the unit spectral edge algebraically. -/
theorem cutoff_gap_value (N : ℕ) :
    1 - ((1 : ℝ) - 1 / (N + 1 : ℝ)) = 1 / (N + 1 : ℝ) := by
  ring

/-- A common exponential physical bound is exactly a lower mass-gap bound
before any operator limit is taken. -/
theorem physical_gap_from_common_base
    (q a m : ℝ)
    (ha : 0 < a)
    (hq : q ≤ Real.exp (-m * a))
    (hqpos : 0 < q) :
    m ≤ -Real.log q / a := by
  have hlog : Real.log q ≤ -m * a := by
    have := Real.log_le_iff hqpos
    rw [this]
    simpa using hq
  have hneg : m * a ≤ -Real.log q := by linarith
  exact (le_div_iff₀ ha).2 hneg

/-- A cutoff-dependent dimensionless gap is not a uniform bound when its
infimum is zero. -/
theorem positive_each_not_uniform
    (gap : ℕ → ℝ)
    (hpos : ∀ n, 0 < gap n)
    (hsmall : ∀ epsilon > 0, ∃ n, gap n < epsilon) :
    ¬ ∃ c > 0, ∀ n, c ≤ gap n := by
  rintro ⟨c, hc, hall⟩
  obtain ⟨n, hn⟩ := hsmall c hc
  exact (not_lt_of_ge (hall n)) hn

end YangMillsBraid
