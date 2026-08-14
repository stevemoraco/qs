import Mathlib

/-!
# RG direction firewall for continuum Yang--Mills scale arguments

This file records two finite facts that are load-bearing when an RG proof
transports a lattice spectral gap to a continuum physical mass scale.

1. A forward step whose leading beta-function contribution is `+ b u^2`, with
   `b > 0`, strictly increases a positive coupling. This remains true under a
   higher-order perturbation whose absolute size is at most half the leading
   quadratic increment.
2. An upper envelope `x ≤ y` cannot be reversed into the lower bound `y ≤ x`.

These are deliberately elementary firewall lemmas. They are useful for
checking the orientation of a claimed RG recurrence and the direction of a
sum comparison. They do not formalize any source paper, do not prove a
Yang--Mills beta function, do not prove a mass gap, and do not establish an
Osterwalder--Schrader continuum limit.
-/

namespace Millennium.YangMills

/-- Exact positive-quadratic forward RG model step. -/
def positiveQuadraticRGStep (b u : ℝ) : ℝ :=
  u + b * u^2

/-- A positive one-loop coefficient makes the positive-quadratic forward step
strictly increase every positive coupling. -/
theorem positive_quadratic_rg_step_strictly_increases
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    u < positiveQuadraticRGStep b u := by
  unfold positiveQuadraticRGStep
  have hinc : 0 < b * u^2 := by positivity
  linarith

/-- Consequently the same positive-quadratic forward step cannot at once be
used as a monotone-decreasing asymptotically-free trajectory in the same index
direction. -/
theorem positive_quadratic_rg_step_not_nonincreasing
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ¬ positiveQuadraticRGStep b u ≤ u := by
  exact not_le_of_gt (positive_quadratic_rg_step_strictly_increases b u hb hu)

/-- The sign conclusion is stable under a genuinely higher-order error: if the
error is at most half of the leading positive quadratic increment, the forward
step still strictly increases. -/
theorem positive_quadratic_with_small_remainder_strictly_increases
    (b u r : ℝ) (hb : 0 < b) (hu : 0 < u)
    (hr : |r| ≤ (b / 2) * u^2) :
    u < u + b * u^2 + r := by
  have hhalf : 0 < (b / 2) * u^2 := by positivity
  have hrlo : -((b / 2) * u^2) ≤ r := (abs_le.mp hr).1
  nlinarith

/-- Exact inverse-coupling sign for the positive-quadratic model: the inverse
coupling decreases in the same forward index direction. -/
theorem positive_quadratic_inverse_difference_identity
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    1 / positiveQuadraticRGStep b u - 1 / u = -b / (1 + b * u) := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hfacpos : 0 < 1 + b * u := by positivity
  have hfac0 : 1 + b * u ≠ 0 := ne_of_gt hfacpos
  unfold positiveQuadraticRGStep
  have hstep : u + b * u^2 = u * (1 + b * u) := by ring
  rw [hstep]
  field_simp [hu0, hfac0]
  ring

/-- Therefore the inverse coupling has strictly negative one-step drift for a
positive-quadratic forward RG step. -/
theorem positive_quadratic_inverse_difference_negative
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    1 / positiveQuadraticRGStep b u - 1 / u < 0 := by
  rw [positive_quadratic_inverse_difference_identity b u hb hu]
  have hfacpos : 0 < 1 + b * u := by positivity
  have hbneg : -b < 0 := by linarith
  exact div_neg_of_neg_of_pos hbneg hfacpos

/-- Minimal arithmetic counterexample to reversing an upper bound into a lower
bound. This is the finite logical firewall for sum-comparison steps. -/
theorem upper_envelope_does_not_reverse :
    (1 / 4 : ℝ) ≤ 1 / 2 ∧ ¬ ((1 / 2 : ℝ) ≤ 1 / 4) := by
  norm_num

#print axioms positive_quadratic_rg_step_strictly_increases
#print axioms positive_quadratic_rg_step_not_nonincreasing
#print axioms positive_quadratic_with_small_remainder_strictly_increases
#print axioms positive_quadratic_inverse_difference_identity
#print axioms positive_quadratic_inverse_difference_negative
#print axioms upper_envelope_does_not_reverse

end Millennium.YangMills
