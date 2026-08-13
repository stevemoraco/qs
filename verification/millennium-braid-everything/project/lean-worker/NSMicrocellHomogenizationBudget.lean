import Mathlib

namespace NSMicrocellHomogenizationBudget

/-- Active child cells per active parent cell exponent. -/
theorem active_ratio_exponent (alpha b : ℝ) :
    b*(5-2*alpha) - (5-2*alpha) = (b-1)*(5-2*alpha) := by ring

/-- Fine geometric cells per parent carrier cell exponent. -/
theorem fine_cell_exponent (b : ℝ) :
    3*b - 3 = 3*(b-1) := by ring

/-- Geometric placement slack after reserving the active intermittent child cells. -/
theorem placement_slack_factor (alpha b : ℝ) :
    3*(b-1) - (b-1)*(5-2*alpha)
      = 2*(b-1)*(alpha-1) := by ring

/-- The active-child-per-parent exponent is strictly positive in the strict physical window. -/
theorem active_ratio_pos
    {alpha b : ℝ} (ha : alpha < (5:ℝ)/2) (hb : 1 < b) :
    0 < (b-1)*(5-2*alpha) := by
  exact mul_pos (sub_pos.mpr hb) (by linarith)

/-- The geometric placement slack is strictly positive for alpha>1 and b>1. -/
theorem placement_slack_pos
    {alpha b : ℝ} (ha : 1 < alpha) (hb : 1 < b) :
    0 < 2*(b-1)*(alpha-1) := by positivity

#print axioms active_ratio_exponent
#print axioms fine_cell_exponent
#print axioms placement_slack_factor
#print axioms active_ratio_pos
#print axioms placement_slack_pos

end NSMicrocellHomogenizationBudget
