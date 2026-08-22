import Mathlib

namespace Millennium.RH.ChebyshevPositiveBregman

noncomputable def positivePart (x : ℝ) : ℝ := max x 0

noncomputable def positiveEnergy (x : ℝ) : ℝ := positivePart x ^ 2 / 2

noncomputable def bregmanResidual (a b : ℝ) : ℝ :=
  positivePart b * (b - a) - (positiveEnergy b - positiveEnergy a)

theorem bregmanResidual_nonneg (a b : ℝ) :
    0 ≤ bregmanResidual a b := by
  unfold bregmanResidual positiveEnergy positivePart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg (b - a)]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha' hb
      nlinarith
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [max_eq_right hb']
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      positivity
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      norm_num

#print axioms bregmanResidual_nonneg

end Millennium.RH.ChebyshevPositiveBregman
