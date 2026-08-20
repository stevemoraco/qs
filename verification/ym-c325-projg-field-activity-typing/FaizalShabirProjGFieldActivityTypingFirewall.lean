import Mathlib

/-!
# Proj_G field-size versus activity-size firewall

Finite scalar bookkeeping for C325.

The source-level issue is a type distinction: a nearest-group projection correction
can be second order in an independent local field/chart size without being quadratic
in an unrelated polymer activity norm. The repaired fixed-terminal-scale route may
instead pay such a correction as a fixed additive local budget.

This file does not formalize SU(N), the polar map, BKAR, polymer activities,
reflection positivity, a Yang--Mills RG step, a mass gap, or the Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirProjGFieldActivityTypingFirewall

/-- A strictly positive correction present at zero activity cannot satisfy a
uniform bound by `C * activity^2`. -/
theorem positive_field_correction_not_activity_quadratic
    (C projection : ℝ)
    (hprojection : 0 < projection) :
    ¬ projection ≤ C * (0 : ℝ) ^ 2 := by
  simpa using (not_le.mpr hprojection)

/-- Four independent nonnegative one-step budgets, each no larger than a
quarter of the invariant radius, fit inside that radius. -/
theorem four_way_invariant_budget
    (quadratic largeField projection genuineResidual radius : ℝ)
    (hquadratic : quadratic ≤ radius / 4)
    (hlarge : largeField ≤ radius / 4)
    (hprojection : projection ≤ radius / 4)
    (hgenuine : genuineResidual ≤ radius / 4) :
    quadratic + largeField + projection + genuineResidual ≤ radius := by
  linarith

/-- A field-quadratic projection estimate can be consumed as one fixed quarter
of an invariant-ball budget without identifying field size with activity size. -/
theorem field_quadratic_projection_fits_quarter_budget
    (C δ radius : ℝ)
    (hbudget : C * δ ^ 2 ≤ radius / 4) :
    C * δ ^ 2 ≤ radius / 4 := hbudget

#print axioms positive_field_correction_not_activity_quadratic
#print axioms four_way_invariant_budget
#print axioms field_quadratic_projection_fits_quarter_budget

end Millennium.YangMills.FaizalShabirProjGFieldActivityTypingFirewall
