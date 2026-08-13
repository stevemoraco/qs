import Mathlib

namespace SixLaneAudit.PointwiseUniformityObstruction

/-- A staircase family whose `k`-th row is exactly equal to the positive
reference value `1` from index `k` onward. -/
def staircase (k n : ℕ) : ℝ := if k ≤ n then 1 else 0

/-- Every fixed row has an exact positive tail. -/
theorem exact_tail (k : ℕ) :
    ∀ n, k ≤ n → staircase k n = 1 := by
  intro n hkn
  simp [staircase, hkn]

/-- Strong pointwise convergence: for each parameter `k`, the error from the
positive reference value is eventually identically zero. -/
theorem pointwise_exact_tail :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → |staircase k n - 1| = 0 := by
  intro k
  refine ⟨k, ?_⟩
  intro n hkn
  rw [exact_tail k n hkn]
  norm_num

/-- At every candidate common cutoff `N`, the next row is still zero at `N`. -/
theorem zero_at_every_candidate_cutoff (N : ℕ) :
    staircase (N + 1) N = 0 := by
  have hnot : ¬ N + 1 ≤ N := by omega
  simp [staircase, hnot]

/-- Quantifier-order obstruction: exact positive tails row-by-row do not imply
one cutoff that makes all rows positive simultaneously. -/
theorem no_uniform_positive_tail :
    ¬ ∃ N : ℕ, ∀ k n : ℕ, N ≤ n → 0 < staircase k n := by
  rintro ⟨N, hN⟩
  have hbad : 0 < staircase (N + 1) N := hN (N + 1) N (by omega)
  rw [zero_at_every_candidate_cutoff N] at hbad
  norm_num at hbad

/-- Even convergence that is eventually exact for every fixed parameter does
not supply a uniform half-margin over the whole parameter family.  A separate
uniformity theorem (compactness/equicontinuity/coercivity/etc., depending on the
application) is genuinely required to commute `∀ k, ∃ N` into `∃ N, ∀ k`. -/
theorem pointwise_positive_limit_not_uniform_half_margin :
    (∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → |staircase k n - 1| = 0) ∧
      ¬ ∃ N : ℕ, ∀ k n : ℕ, N ≤ n → (1 : ℝ) / 2 < staircase k n := by
  constructor
  · exact pointwise_exact_tail
  · rintro ⟨N, hN⟩
    have hbad : (1 : ℝ) / 2 < staircase (N + 1) N :=
      hN (N + 1) N (by omega)
    rw [zero_at_every_candidate_cutoff N] at hbad
    norm_num at hbad

#print axioms exact_tail
#print axioms pointwise_exact_tail
#print axioms zero_at_every_candidate_cutoff
#print axioms no_uniform_positive_tail
#print axioms pointwise_positive_limit_not_uniform_half_margin

end SixLaneAudit.PointwiseUniformityObstruction
