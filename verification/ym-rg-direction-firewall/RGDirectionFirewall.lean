import Mathlib

/-!
# RG direction firewall for continuum Yang--Mills scale arguments

This file records finite facts that are load-bearing when an RG proof
transports a lattice spectral gap to a continuum physical mass scale.

1. A forward step whose leading beta-function contribution is `+ b u^2`, with
   `b > 0`, strictly increases a positive coupling. This remains true under a
   higher-order perturbation whose absolute size is at most half the leading
   quadratic increment.
2. A uniform `O(u^4)` recurrence error preserves a quantitative quadratic
   growth lower bound on every fixed weak-coupling interval once its constant
   is small relative to the leading coefficient.
3. An upper envelope `x ≤ y` cannot be reversed into the lower bound `y ≤ x`.
4. Pointwise positivity of a family of gaps is logically weaker than a
   regulator/volume-uniform positive lower bound.

These are deliberately elementary firewall lemmas. They are useful for
checking the orientation of a claimed RG recurrence and the quantifiers of a
spectral-gap argument. They do not formalize any source paper, do not prove a
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

/-- On a fixed interval `0 < u ≤ U`, a uniform quartic error bound
`|r| ≤ R u^4` is at most half the leading quadratic increment whenever
`R U^2 ≤ b/2`. -/
theorem quartic_remainder_le_half_quadratic
    (b R u U r : ℝ)
    (hR : 0 ≤ R) (hu : 0 < u) (huU : u ≤ U)
    (hRU : R * U^2 ≤ b / 2)
    (hr : |r| ≤ R * u^4) :
    |r| ≤ (b / 2) * u^2 := by
  have hU : 0 < U := lt_of_lt_of_le hu huU
  have hsq : u^2 ≤ U^2 := by nlinarith
  have hRu2 : R * u^2 ≤ b / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hsq hR) hRU
  have hquartic : R * u^4 ≤ (b / 2) * u^2 := by
    calc
      R * u^4 = (R * u^2) * u^2 := by ring
      _ ≤ (b / 2) * u^2 :=
        mul_le_mul_of_nonneg_right hRu2 (sq_nonneg u)
  exact le_trans hr hquartic

/-- Therefore an `O(u^4)` perturbation preserves an explicit quadratic growth
budget. This is the growth hypothesis needed by the accumulated-remainder
theorem after restricting to a fixed weak-coupling threshold. -/
theorem quartic_remainder_preserves_quadratic_growth
    (b R u U r : ℝ)
    (hR : 0 ≤ R) (hu : 0 < u) (huU : u ≤ U)
    (hRU : R * U^2 ≤ b / 2)
    (hr : |r| ≤ R * u^4) :
    (b / 2) * u^2 ≤ (u + b * u^2 + r) - u := by
  have hhalf := quartic_remainder_le_half_quadratic
    b R u U r hR hu huU hRU hr
  have hrlo : -((b / 2) * u^2) ≤ r := (abs_le.mp hhalf).1
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

/-- Scalar countermodel for the quantifier jump from pointwise positivity to a
uniform positive lower bound: the family `gap(x)=x` is positive at every
positive parameter but has no positive lower bound over all positive
parameters. -/
theorem pointwise_positive_gap_not_uniform :
    (∀ x : ℝ, 0 < x → 0 < x) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → c ≤ x := by
  constructor
  · intro x hx
    exact hx
  · rintro ⟨c, hc, huniform⟩
    have hx : 0 < c / 2 := by linarith
    have hbad := huniform (c / 2) hx
    linarith

#print axioms positive_quadratic_rg_step_strictly_increases
#print axioms positive_quadratic_rg_step_not_nonincreasing
#print axioms positive_quadratic_with_small_remainder_strictly_increases
#print axioms quartic_remainder_le_half_quadratic
#print axioms quartic_remainder_preserves_quadratic_growth
#print axioms positive_quadratic_inverse_difference_identity
#print axioms positive_quadratic_inverse_difference_negative
#print axioms upper_envelope_does_not_reverse
#print axioms pointwise_positive_gap_not_uniform

end Millennium.YangMills
