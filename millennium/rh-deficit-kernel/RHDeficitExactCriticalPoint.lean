import Mathlib

namespace RHDeficitExactCriticalPoint

/-- Positive root of the smooth-piece slope numerator
`4 y^2 - 2 y - K`, where `y = sqrt x`. -/
noncomputable def criticalRoot (K : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * K)) / 4

/-- Numerator of `x * Delta'(x)` after the substitution `y = sqrt x` on a
prime-power-knot-free interval with constant staircase coefficient `K`. -/
def slopeNumerator (K y : ℝ) : ℝ :=
  4 * y ^ 2 - 2 * y - K

/-- The explicit root satisfies the quadratic equation. -/
theorem criticalRoot_spec
    {K : ℝ}
    (hK : 0 ≤ K) :
    slopeNumerator K (criticalRoot K) = 0 := by
  have hdisc : 0 ≤ 1 + 4 * K := by linarith
  have hsqrt := Real.sq_sqrt hdisc
  unfold slopeNumerator criticalRoot
  nlinarith

/-- For the deficit application `K > 0`, so the positive critical root lies
strictly above `1/2`. -/
theorem criticalRoot_gt_half
    {K : ℝ}
    (hK : 0 < K) :
    (1 : ℝ) / 2 < criticalRoot K := by
  have hdisc : 0 ≤ 1 + 4 * K := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 4 * K) := Real.sqrt_nonneg _
  have hsqrt_sq := Real.sq_sqrt hdisc
  unfold criticalRoot
  nlinarith

/-- Exact factorization around the positive root. -/
theorem slopeNumerator_factor
    {K y : ℝ}
    (hK : 0 ≤ K) :
    slopeNumerator K y =
      (y - criticalRoot K) * (4 * (y + criticalRoot K) - 2) := by
  have hroot := criticalRoot_spec hK
  unfold slopeNumerator at hroot ⊢
  nlinarith

/-- Before the critical root, the smooth-piece slope numerator is negative. -/
theorem slopeNumerator_neg_before
    {K y : ℝ}
    (hK : 0 < K)
    (hy : 0 < y)
    (hyr : y < criticalRoot K) :
    slopeNumerator K y < 0 := by
  have hr : (1 : ℝ) / 2 < criticalRoot K := criticalRoot_gt_half hK
  have hsecond : 0 < 4 * (y + criticalRoot K) - 2 := by linarith
  rw [slopeNumerator_factor (le_of_lt hK)]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hyr) hsecond

/-- After the critical root, the smooth-piece slope numerator is positive. -/
theorem slopeNumerator_pos_after
    {K y : ℝ}
    (hK : 0 < K)
    (hyr : criticalRoot K < y) :
    0 < slopeNumerator K y := by
  have hr : (1 : ℝ) / 2 < criticalRoot K := criticalRoot_gt_half hK
  have hsecond : 0 < 4 * (y + criticalRoot K) - 2 := by linarith
  rw [slopeNumerator_factor (le_of_lt hK)]
  exact mul_pos (sub_pos.mpr hyr) hsecond

/-- The explicit critical root is the unique positive zero of the numerator. -/
theorem positive_zero_unique
    {K y : ℝ}
    (hK : 0 < K)
    (hy : 0 < y)
    (hz : slopeNumerator K y = 0) :
    y = criticalRoot K := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyr | hry
  · have hneg := slopeNumerator_neg_before hK hy hyr
    linarith
  · have hpos := slopeNumerator_pos_after hK hry
    linarith

/-- The smooth primitive on a knot-free interval. Its derivative is the
weighted-Chebyshev deficit slope once the endpoint staircases are fixed. -/
noncomputable def smoothPrimitive (K x : ℝ) : ℝ :=
  4 * x - 4 * Real.sqrt x - K * Real.log x

/-- Exact propagation of the deficit between two positive points in one smooth
piece. The positivity hypotheses are the application domain and discharge the
nonzero conditions in `Real.log_div`. -/
theorem smoothPrimitive_sub
    (K u v : ℝ)
    (hu : 0 < u)
    (hv : 0 < v) :
    smoothPrimitive K v - smoothPrimitive K u =
      4 * (v - u) - 4 * (Real.sqrt v - Real.sqrt u)
        - K * Real.log (v / u) := by
  unfold smoothPrimitive
  rw [Real.log_div hv.ne' hu.ne']
  ring

/-- Order-theoretic firewall for the continuum-to-event reduction: a function
that decreases to `r` and increases after `r` has its minimum at `r`. -/
theorem valley_minimum
    (f : ℝ → ℝ)
    {u r v x : ℝ}
    (hux : u ≤ x)
    (hxv : x ≤ v)
    (hleft : ∀ t, u ≤ t → t ≤ r → f r ≤ f t)
    (hright : ∀ t, r ≤ t → t ≤ v → f r ≤ f t) :
    f r ≤ f x := by
  by_cases hxr : x ≤ r
  · exact hleft x hux hxr
  · have hrx : r ≤ x := le_of_not_ge hxr
    exact hright x hrx hxv

#print axioms criticalRoot_spec
#print axioms criticalRoot_gt_half
#print axioms slopeNumerator_factor
#print axioms slopeNumerator_neg_before
#print axioms slopeNumerator_pos_after
#print axioms positive_zero_unique
#print axioms smoothPrimitive_sub
#print axioms valley_minimum

end RHDeficitExactCriticalPoint
