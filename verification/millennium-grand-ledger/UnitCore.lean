import Mathlib

namespace MillenniumGrandUnit

theorem positive_square_unit_exactification
    (q : ℚ) (hpos : 0 < q) (hsquare : q ^ 2 = 1) : q = 1 := by
  have hfactor : (q - 1) * (q + 1) = 0 := by
    calc
      (q - 1) * (q + 1) = q ^ 2 - 1 := by ring
      _ = 0 := by rw [hsquare]; norm_num
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · linarith
  · linarith

#print axioms positive_square_unit_exactification

end MillenniumGrandUnit
