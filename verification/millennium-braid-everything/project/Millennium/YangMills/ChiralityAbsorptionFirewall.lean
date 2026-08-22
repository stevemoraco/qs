import Mathlib

/-!
# Yang--Mills chirality-absorption firewall

For a four-dimensional curvature decomposed into self-dual and anti-self-dual
parts with squared magnitudes `plus²` and `minus²`, define the one-sided ratio

  δ = minus² / (plus² + minus²).

A nonzero anti-self-dual curvature has `plus = 0`, hence `δ = 1`, not `0`.
Therefore a statement that an ASD bubble automatically drives this particular
ratio to zero selects the wrong chirality.

The file also records that arbitrarily small integrated anti-self-dual energy
on a tiny region is compatible with pointwise ratio one there.  Thus integrated
or W^{1,2}-type convergence alone cannot justify a supremum-ratio bound.

This is scalar real algebra.  It does not formalize bundles, curvature, Bianchi,
Yang--Mills flow, bubbling, quantum fields, or the mass gap.
-/

namespace Millennium.YangMills

/-- One-sided anti-self-dual energy fraction. -/
def chiralityRatio (plus minus : ℝ) : ℝ :=
  minus ^ 2 / (plus ^ 2 + minus ^ 2)

/-- A self-dual state (`minus = 0`) has one-sided ratio zero. -/
theorem selfDual_ratio_zero (plus : ℝ) :
    chiralityRatio plus 0 = 0 := by
  simp [chiralityRatio]

/-- A nonzero anti-self-dual state (`plus = 0`) has one-sided ratio one. -/
theorem antiSelfDual_ratio_one {minus : ℝ} (hminus : minus ≠ 0) :
    chiralityRatio 0 minus = 1 := by
  have hminusSq : minus ^ 2 ≠ 0 := pow_ne_zero 2 hminus
  simp [chiralityRatio, hminusSq]

/-- Consequently, an ASD state cannot simultaneously satisfy `δ = 0`. -/
theorem antiSelfDual_not_ratio_zero {minus : ℝ} (hminus : minus ≠ 0) :
    chiralityRatio 0 minus ≠ 0 := by
  rw [antiSelfDual_ratio_one hminus]
  norm_num

/--
Arbitrarily small integrated minus-energy on a region of small positive mass is
compatible with maximal pointwise chirality ratio on that region.  This is the
scalar core of the warning that integral convergence does not imply a supremum
ratio estimate when the denominator can change chirality locally.
-/
theorem localizedSpike_smallIntegral_maxRatio
    {ε : ℝ} (hε : 0 < ε) :
    ∃ mass plus minus : ℝ,
      0 < mass ∧
      mass * minus ^ 2 < ε ∧
      chiralityRatio plus minus = 1 := by
  refine ⟨ε / 2, 0, 1, ?_, ?_, ?_⟩
  · linarith
  · norm_num
    linarith
  · norm_num [chiralityRatio]

/-- The one-sided ratio distinguishes the two duality orientations exactly. -/
theorem opposite_chiralities_have_opposite_ratios
    {plus minus : ℝ} (hplus : plus ≠ 0) (hminus : minus ≠ 0) :
    chiralityRatio plus 0 = 0 ∧ chiralityRatio 0 minus = 1 := by
  exact ⟨selfDual_ratio_zero plus, antiSelfDual_ratio_one hminus⟩

#print axioms chiralityRatio
#print axioms selfDual_ratio_zero
#print axioms antiSelfDual_ratio_one
#print axioms antiSelfDual_not_ratio_zero
#print axioms localizedSpike_smallIntegral_maxRatio
#print axioms opposite_chiralities_have_opposite_ratios

end Millennium.YangMills
