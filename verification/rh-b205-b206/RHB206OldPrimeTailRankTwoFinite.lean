import Mathlib

/-!
# RH B206 old-prime tail rank-two finite core

Finite algebra behind the B206 coefficient-geometry reduction.
-/

namespace RHB206OldPrimeTailRankTwoFinite

def oldCoeff (A h p : ℝ) : ℝ := A / p - h

theorem oldCoeff_decomposition (A h p : ℝ) :
    oldCoeff A h p = (1 / p) * A - h := by
  simp [oldCoeff]
  ring

theorem oldCoeff_difference
    {A h p q : ℝ}
    (hp : p ≠ 0)
    (hq : q ≠ 0) :
    oldCoeff A h p - oldCoeff A h q =
      (1 / p - 1 / q) * A := by
  field_simp [oldCoeff, hp, hq]
  <;> ring

theorem cleared_oldCoeff_difference
    {A h p q : ℝ}
    (hp : p ≠ 0)
    (hq : q ≠ 0) :
    p * oldCoeff A h p - q * oldCoeff A h q = (q - p) * h := by
  field_simp [oldCoeff, hp, hq]
  <;> ring

theorem weighted_oldCoeff_decomposition
    {A h p w : ℝ} :
    w * oldCoeff A h p = (w / p) * A - (w * h) := by
  simp [oldCoeff]
  ring

#print axioms oldCoeff_decomposition
#print axioms oldCoeff_difference
#print axioms cleared_oldCoeff_difference
#print axioms weighted_oldCoeff_decomposition

end RHB206OldPrimeTailRankTwoFinite
