import Mathlib

/-!
# Reblocking versus engineering-scaling normalization firewall

Finite scalar algebra behind the source-typing audit of the Faizal--Shabir
weak RG.  In four dimensions a coarse block contains `b^4` fine placements,
while a dimension-six net engineering multiplier is `b^-2`.

If an unnormalised `b^4` reblocking multiplicity is multiplied again by that
*net* engineering factor, the result is `b^2`, not `b^-2`.  Recovering the
net dimension-six multiplier from a literal fine-block sum requires a
compensating `b^-4` density normalization (or an equivalent convention in
which `b^(4-Delta)` is already the combined reblock-plus-rescale factor).

This file proves only scalar normalization identities.  It does not formalize
polymer reblocking, engineering dimensions, gauge fields, RG, Yang--Mills, a
mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.ReblockEngineeringNormalizationFirewall

/-- A four-dimensional raw placement factor followed by a dimension-six
`b^-2` factor grows like `b^2` if the placement factor is charged separately. -/
theorem raw_four_volume_times_dimension_six
    (b : ℝ) (hb : b ≠ 0) :
    b ^ 4 * (b ^ 2)⁻¹ = b ^ 2 := by
  field_simp [hb]

/-- A compensating `b^-4` density normalization restores the net
`b^-2` dimension-six factor. -/
theorem normalized_four_volume_times_dimension_six
    (b : ℝ) (hb : b ≠ 0) :
    b ^ 4 * (b ^ 4)⁻¹ * (b ^ 2)⁻¹ = (b ^ 2)⁻¹ := by
  field_simp [hb]

/-- At dyadic blocking, sixteen raw fine placements times the ideal quarter
engineering factor give four, not a contraction. -/
theorem dyadic_raw_count_overwhelms_quarter :
    (16 : ℝ) * (1 / 4 : ℝ) = 4 := by
  norm_num

/-- At dyadic blocking, the normalized fine-placement average followed by the
quarter engineering factor recovers exactly the quarter multiplier. -/
theorem dyadic_normalized_count_recovers_quarter :
    (16 : ℝ) * (1 / 16 : ℝ) * (1 / 4 : ℝ) = 1 / 4 := by
  norm_num

#print axioms raw_four_volume_times_dimension_six
#print axioms normalized_four_volume_times_dimension_six
#print axioms dyadic_raw_count_overwhelms_quarter
#print axioms dyadic_normalized_count_recovers_quarter

end Millennium.YangMills.ReblockEngineeringNormalizationFirewall
