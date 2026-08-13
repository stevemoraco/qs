import Mathlib
namespace B4Auto20Run16

theorem pnp_common_scaling_preserves_ratio_cross_product
    (a b s : ℝ) :
    (s * b) * a = b * (s * a) := by
  ring

theorem pnp_positive_scaling_preserves_strict_exponent_order
    (a b s : ℝ)
    (hs : 0 < s)
    (hba : b < a) :
    s * b < s * a := by
  nlinarith

theorem pnp_bounded_ratio_caps_padded_target
    (a b s R D k : ℝ)
    (hs : 0 ≤ s)
    (hR : 0 ≤ R)
    (hratio : b ≤ R * a)
    (hverifier : s * a ≤ D)
    (hhard : k ≤ s * b) :
    k ≤ R * D := by
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hratio),
    mul_nonneg hR (sub_nonneg.mpr hverifier)]

#print axioms B4Auto20Run16.pnp_common_scaling_preserves_ratio_cross_product
#print axioms B4Auto20Run16.pnp_positive_scaling_preserves_strict_exponent_order
#print axioms B4Auto20Run16.pnp_bounded_ratio_caps_padded_target
end B4Auto20Run16
