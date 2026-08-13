import Mathlib

namespace RHPoleZeroDualityFinite

theorem firstIdentity (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

#print axioms firstIdentity

end RHPoleZeroDualityFinite
