import Mathlib

/-!
# Faizal--Shabir sigma localization-scale firewall

Finite scalar algebra extracted from a source audit of arXiv:2606.19362v1.

The audited FRD text places the heat-time partition at `t ~ L^(2j) sigma^(-2)`, so the
associated square-root localization scale is proportional to `L^j / sigma`.  The later
kernel/tree formulas instead use a denominator proportional to `L^j * sigma`.  This file
formalizes only the elementary reciprocal-vs-product mismatch and its size at `sigma=1/2`.

It does not formalize the heat kernel, the paper, Yang--Mills, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirSigmaLocalizationFirewall

/-- At `sigma = 1/2`, reciprocal and product localization lengths are already distinct. -/
theorem half_sigma_claimed_vs_heat_length :
    ((1 : ℝ) / (1 / 2 : ℝ)) ≠ (1 : ℝ) * (1 / 2 : ℝ) := by
  norm_num

/-- At `sigma = 1/2`, replacing `L / sigma` by `L * sigma` changes the scale by factor four
for the normalized choice `L = 1`. -/
theorem half_sigma_length_ratio_is_four :
    (((1 : ℝ) / (1 / 2 : ℝ)) / ((1 : ℝ) * (1 / 2 : ℝ))) = 4 := by
  norm_num

/-- General algebraic ratio between the heat-time scale `L / sigma` and the printed product
scale `L * sigma`. -/
theorem reciprocal_product_scale_ratio
    (L sigma : ℝ)
    (hL : L ≠ 0)
    (hsigma : sigma ≠ 0) :
    (L / sigma) / (L * sigma) = 1 / sigma ^ 2 := by
  field_simp [hL, hsigma]

/-- The two scales coincide at the unit normalization `sigma = 1`; this is the exceptional
normalization at which the reciprocal/product typo is invisible. -/
theorem unit_sigma_scales_coincide (L : ℝ) :
    L / (1 : ℝ) = L * (1 : ℝ) := by
  ring

#print axioms half_sigma_claimed_vs_heat_length
#print axioms half_sigma_length_ratio_is_four
#print axioms reciprocal_product_scale_ratio
#print axioms unit_sigma_scales_coincide

end Millennium.YangMills.FaizalShabirSigmaLocalizationFirewall
