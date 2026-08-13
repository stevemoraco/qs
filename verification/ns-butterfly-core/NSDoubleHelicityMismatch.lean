import Mathlib

namespace NSDoubleHelicityMismatch

theorem generation_and_cancellation_force_zero
    {zplus zminus : Real}
    (hgen : 3 * zminus + 2 * zplus = 0)
    (hcancel : 3 * zminus - 2 * zplus = 0) :
    zplus = 0 ∧ zminus = 0 := by
  constructor <;> linarith

theorem generated_p_exterior_residual
    {zplus zminus : Real}
    (hgen : 3 * zminus + 2 * zplus = 0) :
    -6 * zplus + 9 * zminus = -12 * zplus := by
  linarith

theorem generated_q_exterior_residual
    {zplus zminus : Real}
    (hgen : 3 * zminus + 2 * zplus = 0) :
    -8 * zplus + 12 * zminus = -16 * zplus := by
  linarith

theorem nonzero_generation_forces_p_exterior
    {zplus zminus : Real}
    (hgen : 3 * zminus + 2 * zplus = 0)
    (hz : zplus ≠ 0) :
    -6 * zplus + 9 * zminus ≠ 0 := by
  rw [generated_p_exterior_residual hgen]
  exact mul_ne_zero (by norm_num) hz

#print axioms generation_and_cancellation_force_zero
#print axioms generated_p_exterior_residual
#print axioms generated_q_exterior_residual
#print axioms nonzero_generation_forces_p_exterior

end NSDoubleHelicityMismatch
