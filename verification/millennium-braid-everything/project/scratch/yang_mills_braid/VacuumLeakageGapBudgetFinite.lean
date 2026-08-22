import Mathlib

namespace YangMillsBraid

/-- Exact scalar Schur/projection rearrangement: an unprojected lower form
bound `A ≤ r + (1-r) λ` yields the sharp projected Rayleigh lower bound. -/
theorem projected_rayleigh_lower_bound
    (A r lam : ℝ)
    (hr : r < 1)
    (hform : A ≤ r + (1 - r) * lam) :
    (A - r) / (1 - r) ≤ lam := by
  have hden : 0 < 1 - r := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The exact bound is sharp: solving the two-dimensional vacuum/excited
mixture identity recovers equality. -/
theorem vacuum_mixture_exact
    (r lam : ℝ) :
    (r + (1 - r) * lam - r) = (1 - r) * lam := by
  ring

/-- A relative leakage bound `r ≤ q A` converts the exact projection theorem
into the composable multiplicative loss `(1-q) A`. -/
theorem relative_leakage_lower_bound
    (A r q lam : ℝ)
    (hA : 0 ≤ A)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hleak : r ≤ q * A)
    (hlam : 0 ≤ lam)
    (hform : A ≤ r + (1 - r) * lam) :
    (1 - q) * A ≤ lam := by
  have h1 : (1 - q) * A ≤ A - r := by
    nlinarith
  have h2 : A - r ≤ (1 - r) * lam := by
    nlinarith
  have h3 : (1 - r) * lam ≤ lam := by
    nlinarith
  linarith

/-- Qualitative leakage decay does not control the scale-weighted budget:
choosing leakage equal to the spacing makes every weighted term exactly one. -/
theorem vanishing_leakage_weight_is_one
    (a : ℝ) (ha : a ≠ 0) :
    a / a = 1 := by
  exact div_self a ha

/-- The exact inversion algebra behind the coarse-anchor formula. -/
theorem invert_projected_comparison
    (A r lam : ℝ)
    (hr : r < 1)
    (hproj : (A - r) / (1 - r) ≤ lam) :
    A ≤ r + (1 - r) * lam := by
  have hden : 0 < 1 - r := by linarith
  have := (div_le_iff₀ hden).mp hproj
  nlinarith

end YangMillsBraid
