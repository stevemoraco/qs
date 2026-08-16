import Mathlib

namespace Millennium.YangMills.MacrostepNormDistortionFirewall

/-- A finite norm-equivalence factor that is allowed to depend on the macrostep
length can destroy a cubic decay row.  The model factor `L^4` turns `L^-3`
into growth of order `L`. -/
theorem cubic_decay_destroyed_by_L4_distortion
    (L : ℝ) (hL : L ≠ 0) :
    L ^ 4 / L ^ 3 = L := by
  field_simp
  ring

/-- More generally, one extra power in an `L`-dependent distortion cancels an
arbitrary inverse power row and leaves linear growth. -/
theorem power_decay_destroyed_by_one_more_power
    (L : ℝ) (n : ℕ) (hL : L ≠ 0) :
    L ^ (n + 1) / L ^ n = L := by
  rw [pow_succ]
  field_simp

/-- If the distortion has power `q` and the raw row has `q+k` powers of decay,
then exactly `k` powers of decay remain.  This is the finite bookkeeping needed
for a repaired macrostep argument once a polynomial norm-distortion exponent is
proved. -/
theorem polynomial_distortion_leaves_residual_power
    (L : ℝ) (q k : ℕ) (hL : L ≠ 0) :
    L ^ q / L ^ (q + k) = 1 / L ^ k := by
  rw [pow_add]
  field_simp

/-- The concrete hostile model is already above one when `L>1`, despite the
raw cubic row tending to zero. -/
theorem hostile_distorted_cubic_row_not_small
    (L : ℝ) (hL : 1 < L) :
    1 < L ^ 4 / L ^ 3 := by
  rw [cubic_decay_destroyed_by_L4_distortion L (ne_of_gt (lt_trans (by norm_num) hL))]
  exact hL

#print axioms cubic_decay_destroyed_by_L4_distortion
#print axioms power_decay_destroyed_by_one_more_power
#print axioms polynomial_distortion_leaves_residual_power
#print axioms hostile_distorted_cubic_row_not_small

end Millennium.YangMills.MacrostepNormDistortionFirewall
