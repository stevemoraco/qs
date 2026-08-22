import Mathlib

namespace Millennium.NavierStokes

/-- Squared exterior/relay coefficient ratio for the isosceles relay is
    `(1 + c^2) / c^2`, hence strictly larger than one for `c ≠ 0`.
    This is the scalar algebraic core of the exterior-mode firewall. -/
theorem isosceles_exterior_squared_ratio_gt_one (c : ℝ) (hc : c ≠ 0) :
    1 < (1 + c^2) / c^2 := by
  have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
  rw [lt_div_iff₀ hc2]
  nlinarith

/-- Equivalently, the exterior coefficient cannot be made perturbatively
    smaller than the reciprocal relay coefficient by tuning finite nonzero `c`. -/
theorem no_small_exterior_by_c_tuning (c : ℝ) (hc : c ≠ 0) :
    c^2 < 1 + c^2 := by
  nlinarith

end Millennium.NavierStokes
