import Mathlib

/-!
# RH screw-slope scalar firewall

This file formalizes only elementary properties of the model `F(t)=|t|` and
its failure of a dyadic lower-slope threshold.  It does not formalize screw
functions, conditional negative definiteness, von Mangoldt sums, Suzuki's
criterion, the zeta function, or RH.
-/

namespace MillenniumBraid
namespace B2Round41RH

noncomputable def linearModel (t : ℝ) : ℝ := |t|

/-- The model is even. -/
theorem linearModel_even (t : ℝ) :
    linearModel (-t) = linearModel t := by
  simp [linearModel]

/-- The model is nonnegative. -/
theorem linearModel_nonnegative (t : ℝ) :
    0 ≤ linearModel t := by
  exact abs_nonneg t

/-- The model is subadditive. -/
theorem linearModel_subadditive (s t : ℝ) :
    linearModel (s + t) ≤ linearModel s + linearModel t := by
  exact abs_add s t

/-- On the positive ray the exact dyadic increment has slope one. -/
theorem linearModel_dyadic_increment
    {a : ℝ} (ha : 0 ≤ a) :
    linearModel (2 * a) - linearModel a = a := by
  have h2a : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha
  rw [linearModel, abs_of_nonneg h2a, linearModel, abs_of_nonneg ha]
  ring

/-- Any correction smaller than `a` leaves the target `2a-r` strictly above
the model's dyadic increment. -/
theorem corrected_two_slope_threshold_fails
    {a r : ℝ} (ha : 0 < a) (hr : r < a) :
    ¬ (linearModel (2 * a) - linearModel a > 2 * a - r) := by
  rw [linearModel_dyadic_increment (le_of_lt ha)]
  linarith

/-- In particular, a uniformly four-bounded correction cannot save the target
once `a>4`. -/
theorem four_bounded_correction_eventually_fails
    {a r : ℝ} (ha : 4 < a) (hr : r ≤ 4) :
    ¬ (linearModel (2 * a) - linearModel a > 2 * a - r) := by
  apply corrected_two_slope_threshold_fails (by linarith)
  linarith

#print axioms linearModel_even
#print axioms linearModel_nonnegative
#print axioms linearModel_subadditive
#print axioms linearModel_dyadic_increment
#print axioms corrected_two_slope_threshold_fails
#print axioms four_bounded_correction_eventually_fails

end B2Round41RH
end MillenniumBraid
