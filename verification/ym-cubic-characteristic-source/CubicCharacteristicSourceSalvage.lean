import Mathlib

namespace Millennium.YangMills

/-!
# Cubic characteristic-source salvage core

Finite pointwise complex analysis only. No Gaussian integration, Minlos
reconstruction, Osterwalder--Schrader axioms, Yang--Mills, or Clay theorem.
-/

noncomputable def cubicCharacteristicPhase (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * x ^ 3 : ℝ) : ℂ))

theorem cubicCharacteristicExponent_re (t x : ℝ) :
    (Complex.I * ((t * x ^ 3 : ℝ) : ℂ)).re = 0 := by
  simp

theorem cubicCharacteristicPhase_abs (t x : ℝ) :
    Complex.abs (cubicCharacteristicPhase t x) = 1 := by
  rw [cubicCharacteristicPhase, Complex.abs_exp]
  simp

theorem cubicCharacteristicPhase_abs_le_one (t x : ℝ) :
    Complex.abs (cubicCharacteristicPhase t x) ≤ 1 := by
  rw [cubicCharacteristicPhase_abs]

theorem cubicCharacteristicPhase_zero_source (x : ℝ) :
    cubicCharacteristicPhase 0 x = 1 := by
  simp [cubicCharacteristicPhase]

#print axioms cubicCharacteristicExponent_re
#print axioms cubicCharacteristicPhase_abs
#print axioms cubicCharacteristicPhase_abs_le_one
#print axioms cubicCharacteristicPhase_zero_source

end Millennium.YangMills
