import Mathlib

namespace NSRecursiveMicrocellCapacity

/-- Intermittent active volume times the number of wavelength cells gives exponent 5-2alpha in 3D. -/
theorem microcell_exponent (alpha : ℝ) :
    (-2*(alpha-1)) + 3 = 5 - 2*alpha := by ring

/-- Strictly positive microcell-growth exponent is equivalent to alpha<5/2. -/
theorem microcell_growth_iff {alpha : ℝ} :
    0 < 5 - 2*alpha ↔ alpha < (5:ℝ)/2 := by
  constructor <;> intro h <;> linarith

/-- Recursive child-over-parent microcell exponent. -/
theorem recursive_ratio_exponent (alpha b : ℝ) :
    b*(5-2*alpha) - (5-2*alpha) = (b-1)*(5-2*alpha) := by ring

/-- In the strict physical window and with shell growth b>1, recursive microcell slack is positive. -/
theorem recursive_ratio_pos
    {alpha b : ℝ} (ha : alpha < (5:ℝ)/2) (hb : 1 < b) :
    0 < (b-1)*(5-2*alpha) := by
  have h1 : 0 < b-1 := sub_pos.mpr hb
  have h2 : 0 < 5-2*alpha := by linarith
  exact mul_pos h1 h2

#print axioms microcell_exponent
#print axioms microcell_growth_iff
#print axioms recursive_ratio_exponent
#print axioms recursive_ratio_pos

end NSRecursiveMicrocellCapacity
