import Mathlib

namespace FiniteSkewSystem

def dy (s q x : ℝ) : ℝ := -s * q * x

def dz (s p x : ℝ) : ℝ := s * p * x

def dx (s p q y z : ℝ) : ℝ := s * (q * y - p * z)

theorem energyDerivativeZero (s p q x y z : ℝ) :
    x * dx s p q y z + y * dy s q x + z * dz s p x = 0 := by
  simp [dx, dy, dz]
  ring

theorem linearInvariantDerivativeZero (s p q x : ℝ) :
    p * dy s q x + q * dz s p x = 0 := by
  simp [dy, dz]
  ring

theorem differenceDerivative (s p q x : ℝ) :
    q * dy s q x - p * dz s p x =
      -s * (p ^ 2 + q ^ 2) * x := by
  simp [dy, dz]
  ring

theorem harmonicSign (s p q x : ℝ) :
    s * (q * dy s q x - p * dz s p x) =
      -(s ^ 2 * (p ^ 2 + q ^ 2)) * x := by
  simp [dy, dz]
  ring

theorem frequencySquaredNonnegative (s p q : ℝ) :
    0 ≤ s ^ 2 * (p ^ 2 + q ^ 2) := by
  positivity

theorem seededFrequencyBound
    {s p q e : ℝ}
    (hp : p ^ 2 ≤ e ^ 2)
    (hq : q ^ 2 ≤ e ^ 2) :
    s ^ 2 * (p ^ 2 + q ^ 2) ≤ 2 * s ^ 2 * e ^ 2 := by
  have hsum : p ^ 2 + q ^ 2 ≤ 2 * e ^ 2 := by
    nlinarith
  have hs : 0 ≤ s ^ 2 := sq_nonneg s
  have hmul := mul_le_mul_of_nonneg_left hsum hs
  nlinarith

#print axioms energyDerivativeZero
#print axioms linearInvariantDerivativeZero
#print axioms differenceDerivative
#print axioms harmonicSign
#print axioms frequencySquaredNonnegative
#print axioms seededFrequencyBound

end FiniteSkewSystem
