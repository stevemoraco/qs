import Mathlib

namespace RHCriticalHalfLogFinite

/-- Finite algebraic shell of a deterministic half-log drift plus a centered remainder.
The prime sums, Johnston theorem, explicit formula, and RH are deliberately absent. -/
noncomputable def centeredMargin (logScale remainder : ℝ) : ℝ :=
  logScale / 2 + remainder

/-- A uniform lower bound on the centered remainder forces positivity once the
half-log drift exceeds the finite debt. -/
theorem centered_lower_bound_forces_positive
    {logScale remainder debt : ℝ}
    (hscale : 2 * debt < logScale)
    (hrem : -debt ≤ remainder) :
    0 < centeredMargin logScale remainder := by
  unfold centeredMargin
  linarith

/-- Algebraic excess of one normalized prime-gap profile above its quadratic-root point. -/
noncomputable def normalizedGapDifference (root scale : ℝ) : ℝ :=
  (scale - 1) / scale
    + root * (scale - 1) ^ 2 / scale
    - Real.log scale

/-- The normalized gap excess is nonnegative.  The proof uses only
`log scale ≤ scale - 1` and one exact square identity. -/
theorem normalized_gap_difference_nonneg
    {root scale : ℝ}
    (hroot : 1 ≤ root)
    (hscale : 0 < scale) :
    0 ≤ normalizedGapDifference root scale := by
  have hscale0 : scale ≠ 0 := ne_of_gt hscale
  have hlog : Real.log scale ≤ scale - 1 :=
    Real.log_le_sub_one_of_pos hscale
  have hsquare :
      0 ≤ (root - 1) * (scale - 1) ^ 2 / scale := by
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hroot) (sq_nonneg (scale - 1)))
      (le_of_lt hscale)
  have halgebra :
      (scale - 1) / scale
          + root * (scale - 1) ^ 2 / scale
          - (scale - 1)
        = (root - 1) * (scale - 1) ^ 2 / scale := by
    field_simp [hscale0]
    ring
  calc
    0 ≤ (root - 1) * (scale - 1) ^ 2 / scale := hsquare
    _ = (scale - 1) / scale
          + root * (scale - 1) ^ 2 / scale
          - (scale - 1) := halgebra.symm
    _ ≤ (scale - 1) / scale
          + root * (scale - 1) ^ 2 / scale
          - Real.log scale := by linarith
    _ = normalizedGapDifference root scale := rfl

/-- Scalar prime-gap profile in square-root coordinates. -/
noncomputable def gapProfile (theta offset s : ℝ) : ℝ :=
  s + theta / s - offset - Real.log s

/-- Exact scale identity when `theta = root^2 - root`. -/
theorem gap_profile_scale_identity
    {root scale offset : ℝ}
    (hroot : 0 < root)
    (hscale : 0 < scale) :
    gapProfile (root ^ 2 - root) offset (root * scale)
        - gapProfile (root ^ 2 - root) offset root
      = normalizedGapDifference root scale := by
  have hroot0 : root ≠ 0 := ne_of_gt hroot
  have hscale0 : scale ≠ 0 := ne_of_gt hscale
  unfold gapProfile normalizedGapDifference
  rw [Real.log_mul hroot0 hscale0]
  field_simp [hroot0, hscale0]
  ring

/-- The quadratic-root coordinate is a global minimum of the gap profile on the
positive half-line.  This is the derivative-free finite core of the one-point-per-gap theorem. -/
theorem gap_profile_minimum
    {root s offset : ℝ}
    (hroot : 1 ≤ root)
    (hs : 0 < s) :
    gapProfile (root ^ 2 - root) offset root
      ≤ gapProfile (root ^ 2 - root) offset s := by
  have hrootpos : 0 < root := lt_of_lt_of_le zero_lt_one hroot
  have hscale : 0 < s / root := div_pos hs hrootpos
  have hid := gap_profile_scale_identity
    (root := root) (scale := s / root) (offset := offset)
    hrootpos hscale
  have hmul : root * (s / root) = s := by
    field_simp [ne_of_gt hrootpos]
  rw [hmul] at hid
  have hnonneg := normalized_gap_difference_nonneg hroot hscale
  linarith

#print axioms centered_lower_bound_forces_positive
#print axioms normalized_gap_difference_nonneg
#print axioms gap_profile_scale_identity
#print axioms gap_profile_minimum

end RHCriticalHalfLogFinite
