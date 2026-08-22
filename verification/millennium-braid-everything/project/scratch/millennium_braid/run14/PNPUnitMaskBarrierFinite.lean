import Mathlib

/-!
# Finite scalar cores for the UNIT mask-test amplification barrier

This file formalizes only elementary order/algebra consequences from the
mask-test note. It does not formalize Boolean circuits, the code-class counting
argument, the Chen--Li--Yang theorem, or `P != NP`.
-/

namespace MillenniumRun14
namespace PNPUnitMaskBarrier

/-- The exact one-mask pair/triple minimax value is at most `3/5`: if the
triple rejection parameter is `q`, the average pair rejection parameter is
`1 - 2q/3`. -/
theorem one_mask_pair_triple_minimax (q : ℝ) :
    min q (1 - 2 * q / 3) ≤ 3 / 5 := by
  by_cases hq : q ≤ 3 / 5
  · exact le_trans (min_le_left _ _) hq
  · have hq' : 3 / 5 < q := lt_of_not_ge hq
    have hright : 1 - 2 * q / 3 < 3 / 5 := by
      linarith
    exact le_trans (min_le_right _ _) hright.le

/-- The lower-bound constant `1/(8*4^t)` forces at least `(s-3)/2` masks when
the target error is at most `2^{-s}`. This is the logarithmic form after taking
base-two logarithms. -/
theorem mask_count_from_exponent
    (s t : ℝ) (h : s ≤ 2 * t + 3) :
    (s - 3) / 2 ≤ t := by
  linarith

/-- Scalar extraction of the triple-incidence lower bound. The hypotheses are
the summed rejection requirement and the pointwise incidence cap. -/
theorem triple_incidence_lower_bound
    (n eps K : ℝ)
    (hn1 : 1 < n)
    (hreq : (1 - eps) * (n * (n - 1) * (n - 2) / 6)
      ≤ ((n - 1)^2 / 8) * K) :
    (4 / 3 : ℝ) * (1 - eps) * n * (n - 2) / (n - 1) ≤ K := by
  have hpos : 0 < n - 1 := sub_pos.mpr hn1
  have hsquare : 0 < (n - 1)^2 := sq_pos_of_pos hpos
  apply (div_le_iff₀ hpos).2
  have hscale : 0 < (8 : ℝ) / (n - 1) := div_pos (by norm_num) hpos
  nlinarith [mul_le_mul_of_nonneg_left hreq hscale.le]

/-- Passing an incidence lower bound through the corrected direct-forest gate
identity `gates = n - 1 + 2K`. The count is: `n-1` gates for the global OR,
`2|S_r|-1` gates for each separate OR/XOR/equality test, and `t` gates to AND
the `t` tests with the global OR, for a total of `n-1+2K`. -/
theorem direct_forest_gate_transfer
    (n eps K gates : ℝ)
    (hK : (4 / 3 : ℝ) * (1 - eps) * n * (n - 2) / (n - 1) ≤ K)
    (hgates : gates = n - 1 + 2 * K) :
    n - 1 + (8 / 3 : ℝ) * (1 - eps) * n * (n - 2) / (n - 1)
      ≤ gates := by
  rw [hgates]
  linarith

end PNPUnitMaskBarrier
end MillenniumRun14
