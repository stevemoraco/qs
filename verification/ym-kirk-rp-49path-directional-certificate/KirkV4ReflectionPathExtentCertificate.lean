import Mathlib

/-!
Finite reflection-support arithmetic only.  This source does not prove the
Kirk source assertion about the primitive 49-path atlas, an OS theorem,
Yang--Mills existence, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills

theorem temporal_template_positive_half
    (anchor offset : ℤ)
    (hAnchor : 0 ≤ anchor)
    (hOffset : 0 ≤ offset) :
    0 ≤ anchor + offset := by
  omega

theorem spatial_template_positive_half
    (anchor offset : ℤ)
    (hAnchor : 1 ≤ anchor)
    (hOffset : -1 ≤ offset) :
    0 ≤ anchor + offset := by
  omega

theorem spatial_template_positive_half_scaled
    (B anchor offset : ℤ)
    (hB : 0 ≤ B)
    (hAnchor : B ≤ anchor)
    (hOffset : -B ≤ offset) :
    0 ≤ anchor + offset := by
  omega

theorem spatial_boundary_row_requires_fixed_layer :
    (0 : ℤ) + (-1) < 0 := by
  norm_num

theorem temporal_longitudinal_extent_0_2
    (anchor offset : ℤ)
    (hAnchor : 0 ≤ anchor)
    (hOffsetLo : 0 ≤ offset)
    (_hOffsetHi : offset ≤ 2) :
    0 ≤ anchor + offset := by
  omega

theorem spatial_transverse_extent_neg1_1
    (anchor offset : ℤ)
    (hAnchor : 1 ≤ anchor)
    (hOffsetLo : -1 ≤ offset)
    (_hOffsetHi : offset ≤ 1) :
    0 ≤ anchor + offset := by
  omega

#print axioms temporal_template_positive_half
#print axioms spatial_template_positive_half
#print axioms spatial_template_positive_half_scaled
#print axioms spatial_boundary_row_requires_fixed_layer
#print axioms temporal_longitudinal_extent_0_2
#print axioms spatial_transverse_extent_neg1_1

end Millennium.YangMills
