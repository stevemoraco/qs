import Mathlib

namespace RHDeficitEventInterface

/-- Numerator of `x * Delta'(x)` after `y = sqrt x` on one knot-free
weighted-Chebyshev interval. -/
def slopeNumerator (K y : ℝ) : ℝ :=
  4 * y ^ 2 - 2 * y - K

/-- Exact factorization around any specified root. This theorem deliberately
uses only the root equation; it does not import a square-root existence claim. -/
theorem slopeNumerator_factor_from_root
    {K r y : ℝ}
    (hroot : slopeNumerator K r = 0) :
    slopeNumerator K y = (y - r) * (4 * (y + r) - 2) := by
  unfold slopeNumerator at hroot ⊢
  nlinarith

/-- A positive root is forced above `1/2` whenever the interval coefficient is
positive. -/
theorem root_gt_half
    {K r : ℝ}
    (hK : 0 < K)
    (hr : 0 < r)
    (hroot : slopeNumerator K r = 0) :
    (1 : ℝ) / 2 < r := by
  by_contra h
  have hrle : r ≤ (1 : ℝ) / 2 := le_of_not_gt h
  have hfac : 4 * r - 2 ≤ 0 := by linarith
  have hprod : r * (4 * r - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) hfac
  unfold slopeNumerator at hroot
  have heq : r * (4 * r - 2) = K := by nlinarith
  nlinarith

/-- Before a positive root, the smooth-piece slope numerator is negative. -/
theorem slopeNumerator_neg_before
    {K r y : ℝ}
    (hK : 0 < K)
    (hr : 0 < r)
    (hy : 0 < y)
    (hroot : slopeNumerator K r = 0)
    (hyr : y < r) :
    slopeNumerator K y < 0 := by
  have hrhalf : (1 : ℝ) / 2 < r := root_gt_half hK hr hroot
  have hsecond : 0 < 4 * (y + r) - 2 := by linarith
  rw [slopeNumerator_factor_from_root hroot]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hyr) hsecond

/-- After a positive root, the smooth-piece slope numerator is positive. -/
theorem slopeNumerator_pos_after
    {K r y : ℝ}
    (hK : 0 < K)
    (hr : 0 < r)
    (hroot : slopeNumerator K r = 0)
    (hyr : r < y) :
    0 < slopeNumerator K y := by
  have hrhalf : (1 : ℝ) / 2 < r := root_gt_half hK hr hroot
  have hsecond : 0 < 4 * (y + r) - 2 := by linarith
  rw [slopeNumerator_factor_from_root hroot]
  exact mul_pos (sub_pos.mpr hyr) hsecond

/-- Any positive root is unique. -/
theorem positive_root_unique
    {K r y : ℝ}
    (hK : 0 < K)
    (hr : 0 < r)
    (hy : 0 < y)
    (hroot : slopeNumerator K r = 0)
    (hyroot : slopeNumerator K y = 0) :
    y = r := by
  have hrhalf : (1 : ℝ) / 2 < r := root_gt_half hK hr hroot
  have hfactor := slopeNumerator_factor_from_root (K := K) (r := r) (y := y) hroot
  rw [hfactor] at hyroot
  rcases mul_eq_zero.mp hyroot with hdiff | hsecond
  · exact sub_eq_zero.mp hdiff
  · have hpos : 0 < 4 * (y + r) - 2 := by linarith
    exact ((ne_of_gt hpos) hsecond).elim

/-- Smooth primitive for a knot-free interval. The square root and logarithm
are retained as opaque terms in the algebraic propagation theorem below. -/
noncomputable def smoothPrimitive (K x : ℝ) : ℝ :=
  4 * x - 4 * Real.sqrt x - K * Real.log x

/-- Exact propagation without invoking `Real.log_div`; this is the raw form
needed by an event cocycle. -/
theorem smoothPrimitive_sub_raw
    (K u v : ℝ) :
    smoothPrimitive K v - smoothPrimitive K u =
      4 * (v - u) - 4 * (Real.sqrt v - Real.sqrt u)
        - K * (Real.log v - Real.log u) := by
  unfold smoothPrimitive
  ring

/-- Algebraic cocycle law for interval increments. -/
noncomputable def intervalIncrement (K u v : ℝ) : ℝ :=
  smoothPrimitive K v - smoothPrimitive K u

theorem intervalIncrement_add
    (K u v w : ℝ) :
    intervalIncrement K u v + intervalIncrement K v w =
      intervalIncrement K u w := by
  simp [intervalIncrement]

/-- Order-theoretic continuum firewall: decreasing into `r` and increasing out
of `r` reduces the whole interval minimum to the single event candidate `r`. -/
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

#print axioms slopeNumerator_factor_from_root
#print axioms root_gt_half
#print axioms slopeNumerator_neg_before
#print axioms slopeNumerator_pos_after
#print axioms positive_root_unique
#print axioms smoothPrimitive_sub_raw
#print axioms intervalIncrement_add
#print axioms valley_minimum

end RHDeficitEventInterface
