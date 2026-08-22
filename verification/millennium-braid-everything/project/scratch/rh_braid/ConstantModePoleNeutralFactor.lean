import Mathlib

/-!
# Constant-plus-one-mode pole-neutral rational factor

Finite algebraic core of the two-channel RH depth amplifier. No zeta-function
statement is encoded here.
-/

namespace RHBraid

/--
The constant-plus-one-mode pole-neutral coefficient combination factors through
`z^2 + 1/4`, making the explicit-formula pole zeros transparent.
-/
theorem constantModePoleNeutralFactor
    (z k : ℂ)
    (hk : z ^ 2 ≠ k ^ 2) :
    -(1 : ℂ) / 4
        + (k ^ 2 + (1 : ℂ) / 4) * z ^ 2 / (z ^ 2 - k ^ 2)
      = k ^ 2 * (z ^ 2 + (1 : ℂ) / 4) / (z ^ 2 - k ^ 2) := by
  have hk' : z ^ 2 - k ^ 2 ≠ 0 := sub_ne_zero.mpr hk
  field_simp [hk']
  ring

end RHBraid
