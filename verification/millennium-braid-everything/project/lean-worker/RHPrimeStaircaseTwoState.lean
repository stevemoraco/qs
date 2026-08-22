import Mathlib

namespace RHPrimeStaircaseTwoState

/-- Algebraic core of the prime-gap mismatch update. -/
theorem z_step
    (z g L Lnext znext : ℝ)
    (h : znext = z + g - (L + Lnext) / 2) :
    znext - z = g - (L + Lnext) / 2 := by
  linarith

/-- Algebraic core of the Johnston energy kick. -/
theorem h_step
    (Hprev H L z : ℝ)
    (h : H = Hprev + L * z) :
    H - Hprev = L * z := by
  linarith

/-- A negative mismatch produces a negative energy kick when the logarithmic
weight is positive. -/
theorem negative_work
    {L z : ℝ} (hL : 0 < L) (hz : z < 0) :
    L * z < 0 := by
  exact mul_neg_of_pos_of_neg hL hz

/-- A positive mismatch produces a positive energy kick when the logarithmic
weight is positive. -/
theorem positive_work
    {L z : ℝ} (hL : 0 < L) (hz : 0 < z) :
    0 < L * z := by
  exact mul_pos hL hz

/-- Exact one-step safety-margin criterion: if the adverse work is smaller than
available margin, positivity survives the step. -/
theorem positive_margin_survives
    {Hprev L z margin : ℝ}
    (hH : margin ≤ Hprev)
    (hm : 0 ≤ margin + L * z) :
    0 ≤ Hprev + L * z := by
  linarith

#print axioms z_step
#print axioms h_step
#print axioms negative_work
#print axioms positive_work
#print axioms positive_margin_survives

end RHPrimeStaircaseTwoState
