import Mathlib

namespace Millennium.YangMills

def cubicRGStep (b c u : ℝ) : ℝ :=
  u * (1 + b * u + c * u^2)

theorem cubicRGStep_ge_input
    (b c u : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u) :
    u ≤ cubicRGStep b c u := by
  have hD : 1 ≤ 1 + b * u + c * u^2 := by
    have hbu : 0 ≤ b * u := mul_nonneg (le_of_lt hb) (le_of_lt hu)
    have hcu2 : 0 ≤ c * u^2 := mul_nonneg hc (sq_nonneg u)
    linarith
  unfold cubicRGStep
  simpa using mul_le_mul_of_nonneg_left hD (le_of_lt hu)

theorem quartic_remainder_le_half_input
    (u r R : ℝ)
    (hu : 0 < u)
    (hr : |r| ≤ R * u^4)
    (hsmall : R * u^3 ≤ (1 : ℝ) / 2) :
    |r| ≤ u / 2 := by
  calc
    |r| ≤ R * u^4 := hr
    _ = (R * u^3) * u := by ring
    _ ≤ ((1 : ℝ) / 2) * u :=
      mul_le_mul_of_nonneg_right hsmall (le_of_lt hu)
    _ = u / 2 := by ring

theorem quartic_perturbed_step_pos
    (b c u r R : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u)
    (hr : |r| ≤ R * u^4)
    (hsmall : R * u^3 ≤ (1 : ℝ) / 2) :
    0 < cubicRGStep b c u + r := by
  have hw : u ≤ cubicRGStep b c u :=
    cubicRGStep_ge_input b c u hb hc hu
  have hrhalf : |r| ≤ u / 2 :=
    quartic_remainder_le_half_input u r R hu hr hsmall
  have hrlower : -|r| ≤ r := neg_abs_le r
  have hu2 : 0 < u / 2 := by positivity
  linarith

theorem quartic_step_product_lower_bound
    (b c u r R : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u)
    (hr : |r| ≤ R * u^4)
    (hsmall : R * u^3 ≤ (1 : ℝ) / 2) :
    u^2 / 2 ≤ (cubicRGStep b c u + r) * cubicRGStep b c u := by
  have hw : u ≤ cubicRGStep b c u :=
    cubicRGStep_ge_input b c u hb hc hu
  have hwpos : 0 < cubicRGStep b c u := lt_of_lt_of_le hu hw
  have hrhalf : |r| ≤ u / 2 :=
    quartic_remainder_le_half_input u r R hu hr hsmall
  have hrlower : -|r| ≤ r := neg_abs_le r
  have hvhalf : u / 2 ≤ cubicRGStep b c u + r := by
    linarith
  have hvnonneg : 0 ≤ cubicRGStep b c u + r := by
    have : 0 < u / 2 := by positivity
    linarith
  calc
    u^2 / 2 = (u / 2) * u := by ring
    _ ≤ (cubicRGStep b c u + r) * u :=
      mul_le_mul_of_nonneg_right hvhalf (le_of_lt hu)
    _ ≤ (cubicRGStep b c u + r) * cubicRGStep b c u :=
      mul_le_mul_of_nonneg_left hw hvnonneg

theorem quartic_remainder_le_half_quadratic
    (b u r R : ℝ)
    (hu : 0 < u)
    (hr : |r| ≤ R * u^4)
    (hsmall : R * u^2 ≤ b / 2) :
    |r| ≤ (b / 2) * u^2 := by
  calc
    |r| ≤ R * u^4 := hr
    _ = (R * u^2) * u^2 := by ring
    _ ≤ (b / 2) * u^2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg u)

theorem quartic_perturbed_step_quadratic_growth
    (b c u r R : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u)
    (hr : |r| ≤ R * u^4)
    (hsmall : R * u^2 ≤ b / 2) :
    (b / 2) * u^2 ≤ (cubicRGStep b c u + r) - u := by
  have hrquad : |r| ≤ (b / 2) * u^2 :=
    quartic_remainder_le_half_quadratic b u r R hu hr hsmall
  have hrlower : -|r| ≤ r := neg_abs_le r
  have hcu3 : 0 ≤ c * u^3 := by
    have hu0 : 0 ≤ u := le_of_lt hu
    exact mul_nonneg hc (by positivity)
  have hstep : cubicRGStep b c u - u = b * u^2 + c * u^3 := by
    unfold cubicRGStep
    ring
  rw [show (cubicRGStep b c u + r) - u =
      (cubicRGStep b c u - u) + r by ring, hstep]
  nlinarith

theorem quartic_perturbation_core_stability
    (b c u r R : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u)
    (hr : |r| ≤ R * u^4)
    (hposSmall : R * u^3 ≤ (1 : ℝ) / 2)
    (hgrowthSmall : R * u^2 ≤ b / 2) :
    0 < cubicRGStep b c u + r ∧
      (b / 2) * u^2 ≤ (cubicRGStep b c u + r) - u := by
  constructor
  · exact quartic_perturbed_step_pos b c u r R hb hc hu hr hposSmall
  · exact quartic_perturbed_step_quadratic_growth
      b c u r R hb hc hu hr hgrowthSmall

#print axioms cubicRGStep_ge_input
#print axioms quartic_remainder_le_half_input
#print axioms quartic_perturbed_step_pos
#print axioms quartic_step_product_lower_bound
#print axioms quartic_remainder_le_half_quadratic
#print axioms quartic_perturbed_step_quadratic_growth
#print axioms quartic_perturbation_core_stability

end Millennium.YangMills
