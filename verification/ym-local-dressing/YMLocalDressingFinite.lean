import Mathlib

namespace YMLocalDressingFinite

/-- If `s = sqrt (M^2 + 4 eps^2)` in the algebraic sense and `M ≥ 1`,
    then the dressed one-site excitation gap is at least one. -/
theorem dressed_gap_ge_one
    {M eps s : ℝ}
    (hM : 1 ≤ M)
    (hs0 : 0 ≤ s)
    (hs : s ^ 2 = M ^ 2 + 4 * eps ^ 2) :
    1 + (s - M) / 2 ≥ 1 := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hsM : M ≤ s := by
    nlinarith [sq_nonneg eps]
  linarith

/-- The lower eigenvalue of the mixed `0/M` block is nonpositive. -/
theorem lower_level_nonpositive
    {M s : ℝ}
    (h : M ≤ s) :
    (M - s) / 2 ≤ 0 := by
  linarith

/-- The square of a sum of `L` orthogonal equal-amplitude creation channels
    is the volume times the one-channel square. -/
theorem orthogonal_creation_square
    (L : ℕ) (eps : ℝ) :
    (L : ℝ) * eps ^ 2 = ∑ _k ∈ Finset.range L, eps ^ 2 := by
  simp

/-- Any proposed fixed global squared cross bound is exceeded once the volume
    is large enough. This is the scalar endpoint of the `sqrt(volume)` law. -/
theorem fixed_cross_bound_fails
    {L : ℕ} {eps C : ℝ}
    (h : C ^ 2 < (L : ℝ) * eps ^ 2) :
    ¬ ((L : ℝ) * eps ^ 2 ≤ C ^ 2) := by
  linarith

/-- The second-order bare Schur payment is extensive when each site contributes
    the same positive amount. -/
theorem extensive_schur_payment
    (L : ℕ) (eps M : ℝ) :
    (L : ℝ) * (eps ^ 2 / M) = ((L : ℝ) * eps ^ 2) / M := by
  ring

/-- A relative defect smaller than a local gap leaves a positive residual gap. -/
theorem local_defect_budget
    {gap defect : ℝ}
    (hgap : 0 < gap)
    (hdef : defect < gap) :
    0 < gap - defect := by
  linarith

#print axioms dressed_gap_ge_one
#print axioms lower_level_nonpositive
#print axioms orthogonal_creation_square
#print axioms fixed_cross_bound_fails
#print axioms extensive_schur_payment
#print axioms local_defect_budget

end YMLocalDressingFinite
