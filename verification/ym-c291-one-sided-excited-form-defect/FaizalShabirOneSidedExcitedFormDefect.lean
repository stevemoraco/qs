import Mathlib

/-!
# Faizal–Shabir one-sided excited-form defect firewall

The finite scalar consumer only. No Yang–Mills operator theorem is encoded.
-/

namespace Millennium.YangMills.FaizalShabirOneSidedExcitedFormDefect

/-- C288 scalar physical mass-loss consumer, flattened here for public replay. -/
theorem one_step_mass_loss_budget
    (lambdaNext m delta aNext eta : ℝ)
    (hstep : lambdaNext ≤ Real.exp (-m * aNext) + eta)
    (hbudget :
      eta ≤
        Real.exp (-(m - delta) * aNext) -
        Real.exp (-m * aNext)) :
    lambdaNext ≤ Real.exp (-(m - delta) * aNext) := by
  linarith

/-- Even a positive subtracted term can increase the norm of a vector. -/
theorem positive_subtraction_can_increase_norm :
    |((0 : ℝ) - 1 + 0)| > |(0 : ℝ)| + |(0 : ℝ)| := by
  norm_num

/-- Bound only harmful one-sided form contributions. -/
theorem one_sided_form_upper_bound
    (idealForm dForm eForm lambdaIdeal deltaD deltaE : ℝ)
    (hIdeal : idealForm ≤ lambdaIdeal)
    (hD : -dForm ≤ deltaD)
    (hE : eForm ≤ deltaE) :
    idealForm - dForm + eForm ≤ lambdaIdeal + deltaD + deltaE := by
  linarith

/-- A genuinely nonnegative subtracted form costs zero in the upper-form budget. -/
theorem nonnegative_subtracted_form_costs_zero
    (dForm : ℝ)
    (hD : 0 ≤ dForm) :
    -dForm ≤ 0 := by
  linarith

/-- A nonpositive remainder form costs zero in the upper-form budget. -/
theorem nonpositive_remainder_form_costs_zero
    (eForm : ℝ)
    (hE : eForm ≤ 0) :
    eForm ≤ 0 := hE

/-- Compose the one-sided form estimate with the physical mass-loss ledger. -/
theorem one_sided_form_mass_loss_budget
    (lambdaNext idealForm dForm eForm lambdaIdeal deltaD deltaE
      m delta aNext : ℝ)
    (hstep : lambdaNext ≤ idealForm - dForm + eForm)
    (hIdeal : idealForm ≤ lambdaIdeal)
    (hD : -dForm ≤ deltaD)
    (hE : eForm ≤ deltaE)
    (hIdealMass : lambdaIdeal ≤ Real.exp (-m * aNext))
    (hbudget :
      deltaD + deltaE ≤
        Real.exp (-(m - delta) * aNext) -
        Real.exp (-m * aNext)) :
    lambdaNext ≤ Real.exp (-(m - delta) * aNext) := by
  have hform :
      idealForm - dForm + eForm ≤ lambdaIdeal + deltaD + deltaE :=
    one_sided_form_upper_bound
      idealForm dForm eForm lambdaIdeal deltaD deltaE hIdeal hD hE
  have hstep' :
      lambdaNext ≤ Real.exp (-m * aNext) + (deltaD + deltaE) := by
    linarith
  exact one_step_mass_loss_budget
    lambdaNext m delta aNext (deltaD + deltaE) hstep' hbudget

#print axioms one_step_mass_loss_budget
#print axioms positive_subtraction_can_increase_norm
#print axioms one_sided_form_upper_bound
#print axioms nonnegative_subtracted_form_costs_zero
#print axioms nonpositive_remainder_form_costs_zero
#print axioms one_sided_form_mass_loss_budget

end Millennium.YangMills.FaizalShabirOneSidedExcitedFormDefect
