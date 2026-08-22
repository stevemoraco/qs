import Mathlib

namespace NSBeltramiLinearizedMargin

/-- The explicit alpha=9/4 master point lies in Palasek's strict parameter window. -/
theorem master_window :
    (1 : ℚ) < 17/16 ∧
    (17/16 : ℚ) < (9/4)/2 ∧
    2*(17/16 : ℚ) < 35/16 ∧
    (35/16 : ℚ) < 9/4 := by
  norm_num

/-- Terminal amplitude exponent d = alpha-beta is exactly 1/16. -/
theorem terminal_decay_exponent :
    (9/4 : ℚ) - 35/16 = 1/16 := by
  norm_num

/-- A generic order-K causal linearized correction has the wrong sign. -/
theorem generic_linearized_exponent :
    -(35/16 : ℚ) + 17/16 + (9/4 - 1) - (17/16)*(1/16) = 15/256 := by
  norm_num

/-- The 3D intermittent envelope exponent at alpha=9/4 is 5/6. -/
theorem envelope_exponent :
    (2 : ℚ) * (9/4 - 1) / 3 = 5/6 := by
  norm_num

/-- After same-helicity Beltrami cancellation demotes K to B, the causal
linearized exponent becomes strictly negative. -/
theorem beltrami_linearized_exponent :
    -(35/16 : ℚ) + 5/6 + (9/4 - 1) - (17/16)*(1/16) = -131/768 := by
  norm_num

/-- The sign flip is strict in exactly the needed directions. -/
theorem correction_sign_flip :
    (0 : ℚ) < 15/256 ∧ (-131/768 : ℚ) < 0 := by
  norm_num

/-- The Beltrami contraction margin is stronger than the current 1/32
master bookkeeping defect exponent. -/
theorem beltrami_margin_beats_master :
    (1/32 : ℚ) < 131/768 := by
  norm_num

#print axioms master_window
#print axioms terminal_decay_exponent
#print axioms generic_linearized_exponent
#print axioms envelope_exponent
#print axioms beltrami_linearized_exponent
#print axioms correction_sign_flip
#print axioms beltrami_margin_beats_master

end NSBeltramiLinearizedMargin
