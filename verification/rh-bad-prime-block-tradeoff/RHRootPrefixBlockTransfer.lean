import Mathlib

namespace RHRootPrefixBlockTransfer

/-- The scalar negative part used by the root and clamped prefix detectors. -/
def negPart (x : ℝ) : ℝ := max (-x) 0

/-- Passing from a clamped response to a smaller unrestricted root response can
only increase the negative excursion. -/
theorem root_negPart_dominates_clamp
    {root clamp : ℝ}
    (h : root ≤ clamp) :
    negPart clamp ≤ negPart root := by
  unfold negPart
  exact max_le_max (neg_le_neg h) le_rfl

/-- A positive factor preserves the sign of the root defect. -/
theorem positive_factor_sign
    {factor root defect : ℝ}
    (hfactor : 0 < factor)
    (hdefect : defect = factor * root) :
    defect < 0 ↔ root < 0 := by
  rw [hdefect]
  constructor
  · intro hproduct
    by_contra hroot
    have hroot_nonneg : 0 ≤ root := le_of_not_gt hroot
    have hproduct_nonneg : 0 ≤ factor * root :=
      mul_nonneg hfactor.le hroot_nonneg
    exact (not_lt_of_ge hproduct_nonneg) hproduct
  · intro hroot
    exact mul_neg_of_pos_of_neg hfactor hroot

/-- A polynomially negative root response transfers quantitatively through a
positive factor. -/
theorem factorized_negative_depth
    {factor root defect depth : ℝ}
    (hfactor : 0 ≤ factor)
    (hdefect : defect = factor * root)
    (hroot : root ≤ -depth) :
    defect ≤ -factor * depth := by
  rw [hdefect]
  have hmul := mul_le_mul_of_nonneg_left hroot hfactor
  nlinarith

/-- The denominator-free defect exponent is the root horizontal depth shifted
by one half, hence the rightmost-zero real-part exponent. -/
theorem rightmost_exponent_shift
    (omega : ℝ) :
    1 / 2 + (omega - 1 / 2) = omega := by
  ring

/-- If the false-RH horizontal depth exceeds twice the escape tolerance, then
the clean bad-block depth `delta-epsilon` exceeds the escape exponent. -/
theorem bad_depth_blocks_escape
    {delta epsilon : ℝ}
    (h : 2 * epsilon < delta) :
    epsilon < delta - epsilon := by
  linarith

/-- Spending one third of the target exponent in each persistence loss leaves
a strictly longer interval exponent than the exact requested subwindow. -/
theorem one_third_loss_contains_exact_window
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    1 - epsilon < 1 - epsilon / 3 - epsilon / 3 := by
  linarith

/-- The one-third loss also retains a stronger depth than the clean reported
`delta-epsilon` threshold. -/
theorem one_third_loss_retains_depth
    {delta epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    delta - epsilon < delta - epsilon / 3 := by
  linarith

/-- A square-root-sized positive factor shifts a root depth exponent `delta`
to `delta+1/2`. -/
theorem square_root_factor_exponent
    (delta epsilon : ℝ) :
    1 / 2 + (delta - epsilon)
      = (1 / 2 + delta) - epsilon := by
  ring

#print axioms root_negPart_dominates_clamp
#print axioms positive_factor_sign
#print axioms factorized_negative_depth
#print axioms rightmost_exponent_shift
#print axioms bad_depth_blocks_escape
#print axioms one_third_loss_contains_exact_window
#print axioms one_third_loss_retains_depth
#print axioms square_root_factor_exponent

end RHRootPrefixBlockTransfer
