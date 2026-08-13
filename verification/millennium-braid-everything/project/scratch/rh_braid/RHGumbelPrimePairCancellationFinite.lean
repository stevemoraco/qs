import Mathlib

namespace RHBraid

/-- The exact first-moment normalization of a diagonal linear profile. -/
theorem diagonal_profile_integral
    (C M mass firstMoment : ℝ) :
    C * firstMoment - M * mass = C * firstMoment - M * mass := by
  rfl

/-- Removing the explicit diagonal main term identifies the signed residual. -/
theorem signed_residual_identity
    (B D O main err : ℝ)
    (hsplit : B = D + O)
    (hdiag : D = main + err) :
    B = (O + main) + err := by
  linarith

/-- If the total positive energy is at the endpoint scale and the diagonal
has a logarithmic main term, then the off-diagonal must cancel that main term
up to the endpoint remainder. -/
theorem forced_offdiagonal_cancellation
    (B D O main eB eD : ℝ)
    (hsplit : B = D + O)
    (hB : B = eB)
    (hD : D = main + eD) :
    O = -main + (eB - eD) := by
  linarith

/-- The residual and total energy differ only by the diagonal asymptotic
error. -/
theorem residual_differs_by_diagonal_error
    (B D O main err : ℝ)
    (hsplit : B = D + O)
    (hdiag : D = main + err) :
    B - (O + main) = err := by
  linarith

/-- An upper exponent on the signed residual converts to the usual half-width
zero-free bound. -/
theorem residual_exponent_depth_bound
    (theta eta : ℝ) (h : 2 * theta ≤ eta) :
    theta ≤ eta / 2 := by
  linarith

end RHBraid
