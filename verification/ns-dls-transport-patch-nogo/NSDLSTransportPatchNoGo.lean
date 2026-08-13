import Mathlib

namespace NSDLSTransportPatchNoGo

/-- In the Palasek parameter window, the exponent counting unit-strain
transport patches is strictly larger than the currently banked DLS
parent-modulation contraction exponent. -/
theorem patchExponent_gt_contractionExponent
    {α β b : ℝ}
    (hb : 1 < b)
    (hβ : 2 * b < β)
    (hα : α < (5 : ℝ) / 2) :
    (b - 1) * (α - β) < β * (b - 1) / b := by
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < b - 1 := sub_pos.mpr hb
  have hβdiv : 2 < β / b := by
    exact (lt_div_iff₀ hb0).2 hβ
  have hdiff : α - β < (1 : ℝ) / 2 := by
    nlinarith
  have hsmall : α - β < β / b := by
    have hhalf : (1 : ℝ) / 2 < 2 := by norm_num
    exact lt_trans hdiff (lt_trans hhalf hβdiv)
  have hmul := mul_lt_mul_of_pos_left hsmall hb1
  calc
    (b - 1) * (α - β) < (b - 1) * (β / b) := hmul
    _ = β * (b - 1) / b := by ring

/-- Equivalent positive exponent gap. -/
theorem patchTax_positive
    {α β b : ℝ}
    (hb : 1 < b)
    (hβ : 2 * b < β)
    (hα : α < (5 : ℝ) / 2) :
    0 < β * (b - 1) / b - (b - 1) * (α - β) := by
  have h := patchExponent_gt_contractionExponent hb hβ hα
  linarith

/-- Exact arithmetic at the banked point α=9/4, b=17/16, β=35/16. -/
theorem explicit_parent_margin :
    ((17 : ℝ) / 16 - 1) * ((9 : ℝ) / 4 - (35 : ℝ) / 16)
      = (1 : ℝ) / 256 := by
  norm_num

/-- Exact unit-strain patch-count exponent at the banked point. -/
theorem explicit_patch_exponent :
    ((35 : ℝ) / 16) * (((17 : ℝ) / 16) - 1) / ((17 : ℝ) / 16)
      = (35 : ℝ) / 272 := by
  norm_num

/-- At the banked point the patch-count exponent strictly exceeds the
one-step parent-frequency contraction exponent. -/
theorem explicit_patch_tax :
    (1 : ℝ) / 256 < (35 : ℝ) / 272 := by
  norm_num

#print axioms patchExponent_gt_contractionExponent
#print axioms patchTax_positive
#print axioms explicit_parent_margin
#print axioms explicit_patch_exponent
#print axioms explicit_patch_tax

end NSDLSTransportPatchNoGo
