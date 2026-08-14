import Mathlib

namespace Millennium.YangMills

/-!
# Any finite incidence charge can be paid by a positive support reserve

After correcting Kirk v4's support exponent from the full source rate to the
available reserve, the compact-collect argument needs a concrete choice of
separation radius. This file proves that every finite nonnegative charge can be
paid by one quarter of any positive reserve, leaving at least one half of the
reserve as terminal exponential decay.

This is finite real algebra. It does not formalize support geometry, polymer
activities, Yang--Mills, a mass gap, or a Clay theorem.
-/

/-- Explicit separation radius for reserve `mu*c` and finite charge `Lambda`. -/
noncomputable def reserveChoiceRadius (mu c Lambda : ℝ) : ℝ :=
  4 * Lambda / (mu * c) + 1

/-- The explicit separation radius is positive and spends at most one quarter
of the reserve on the finite charge. -/
theorem reserveChoiceRadius_pays_quarter
    (mu c Lambda : ℝ)
    (hmu : 0 < mu)
    (hc : 0 < c)
    (hLambda : 0 ≤ Lambda) :
    0 < reserveChoiceRadius mu c Lambda ∧
      Lambda ≤ mu * c * reserveChoiceRadius mu c Lambda / 4 := by
  have hden : 0 < mu * c := mul_pos hmu hc
  have hne : mu * c ≠ 0 := ne_of_gt hden
  constructor
  · unfold reserveChoiceRadius
    have hdiv : 0 ≤ 4 * Lambda / (mu * c) := by positivity
    linarith
  · have hid :
        mu * c * reserveChoiceRadius mu c Lambda / 4 =
          Lambda + mu * c / 4 := by
      unfold reserveChoiceRadius
      field_simp [hne]
      <;> ring
    rw [hid]
    positivity

/-- Spending at most one quarter of the reserve leaves at least half of the
reserve in the exponent `2*Lambda - mu*c*R`. -/
theorem quarter_charge_leaves_half_reserve
    (mu c Lambda R : ℝ)
    (hcharge : Lambda ≤ mu * c * R / 4) :
    2 * Lambda - mu * c * R ≤ -(mu * c * R) / 2 := by
  linarith

/-- Every finite nonnegative charge admits a positive separation radius leaving
one-half reserve decay. -/
theorem exists_radius_paying_finite_charge
    (mu c Lambda : ℝ)
    (hmu : 0 < mu)
    (hc : 0 < c)
    (hLambda : 0 ≤ Lambda) :
    ∃ R : ℝ,
      0 < R ∧
      Lambda ≤ mu * c * R / 4 ∧
      2 * Lambda - mu * c * R ≤ -(mu * c * R) / 2 := by
  let R := reserveChoiceRadius mu c Lambda
  have hpay := reserveChoiceRadius_pays_quarter mu c Lambda hmu hc hLambda
  refine ⟨R, hpay.1, hpay.2, ?_⟩
  exact quarter_charge_leaves_half_reserve mu c Lambda R hpay.2

/-- The surviving half-reserve rate is itself strictly positive. -/
theorem surviving_half_reserve_pos
    (mu c : ℝ)
    (hmu : 0 < mu)
    (hc : 0 < c) :
    0 < mu * c / 2 := by
  positivity

#print axioms reserveChoiceRadius_pays_quarter
#print axioms quarter_charge_leaves_half_reserve
#print axioms exists_radius_paying_finite_charge
#print axioms surviving_half_reserve_pos

end Millennium.YangMills
