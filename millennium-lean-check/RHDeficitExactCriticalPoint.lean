import Mathlib

namespace RHDeficitExactCriticalPoint

noncomputable def criticalRoot (K : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * K)) / 4

def slopeNumerator (K y : ℝ) : ℝ :=
  4 * y ^ 2 - 2 * y - K

theorem criticalRoot_spec
    {K : ℝ}
    (hK : 0 ≤ K) :
    slopeNumerator K (criticalRoot K) = 0 := by
  have hdisc : 0 ≤ 1 + 4 * K := by linarith
  have hsqrt := Real.sq_sqrt hdisc
  unfold slopeNumerator criticalRoot
  nlinarith

theorem criticalRoot_gt_half
    {K : ℝ}
    (hK : 0 < K) :
    (1 : ℝ) / 2 < criticalRoot K := by
  have hdisc : 0 ≤ 1 + 4 * K := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 4 * K) := Real.sqrt_nonneg _
  have hsqrt_sq := Real.sq_sqrt hdisc
  unfold criticalRoot
  nlinarith

theorem slopeNumerator_factor
    {K y : ℝ}
    (hK : 0 ≤ K) :
    slopeNumerator K y =
      (y - criticalRoot K) * (4 * (y + criticalRoot K) - 2) := by
  have hroot := criticalRoot_spec hK
  unfold slopeNumerator at hroot ⊢
  nlinarith

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

theorem slopeNumerator_pos_after
    {K y : ℝ}
    (hK : 0 < K)
    (hyr : criticalRoot K < y) :
    0 < slopeNumerator K y := by
  have hr : (1 : ℝ) / 2 < criticalRoot K := criticalRoot_gt_half hK
  have hsecond : 0 < 4 * (y + criticalRoot K) - 2 := by linarith
  rw [slopeNumerator_factor (le_of_lt hK)]
  exact mul_pos (sub_pos.mpr hyr) hsecond

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

noncomputable def smoothPrimitive (K x : ℝ) : ℝ :=
  4 * x - 4 * Real.sqrt x - K * Real.log x

theorem smoothPrimitive_sub
    (K u v : ℝ) :
    smoothPrimitive K v - smoothPrimitive K u =
      4 * (v - u) - 4 * (Real.sqrt v - Real.sqrt u)
        - K * Real.log (v / u) := by
  unfold smoothPrimitive
  rw [Real.log_div]
  ring

theorem valley_minimum
    (f : ℝ → ℝ)
    {u r v x : ℝ}
    (hur : u ≤ r)
    (hrv : r ≤ v)
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
