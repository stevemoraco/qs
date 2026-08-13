import Mathlib

namespace RHWeightedChebyshevCancellation

/-- Pure algebra behind the cancellation turning the two-window prime expression
into one logarithmic integral. Here `S = -a*A + I` is the Stieltjes
integration-by-parts identity supplied by analysis/arithmetic. -/
theorem two_window_cancels
    {a x r A S I : ℝ}
    (ha : a ≠ 0)
    (hS : S = -a * A + I) :
    16 * (x - r) / a - 8 - 4 * A - (4 / a) * S
      = (4 / a) * (4 * (x - r) - 2 * a - I) := by
  rw [hS]
  field_simp [ha]
  ring

/-- Positivity of the normalized certificate is exactly positivity of the
single deficit once `a>0`. -/
theorem normalized_positive_iff_deficit_positive
    {a deficit : ℝ}
    (ha : 0 < a) :
    0 < (4 / a) * deficit ↔ 0 < deficit := by
  have h4a : 0 < (4 / a : ℝ) := by positivity
  constructor
  · intro h
    exact pos_of_mul_pos_left h (le_of_lt h4a)
  · intro h
    exact mul_pos h4a h

/-- Direct version of the forward positivity implication. -/
theorem deficit_positive_implies_normalized_positive
    {a deficit : ℝ}
    (ha : 0 < a)
    (hd : 0 < deficit) :
    0 < (4 / a) * deficit := by
  positivity

#print axioms two_window_cancels
#print axioms normalized_positive_iff_deficit_positive
#print axioms deficit_positive_implies_normalized_positive

end RHWeightedChebyshevCancellation
