import Mathlib

namespace NSFixedCoefficientRescaling

/-- Algebraic rescaling of a quadratic interaction with fixed coefficient kappa. -/
theorem quadratic_rescale_pair (kappa x y : ℝ) :
    kappa^2 * (x*y) = (kappa*x)*(kappa*y) := by ring

/-- Algebraic rescaling of a quadratic square with fixed coefficient kappa. -/
theorem quadratic_rescale_square (kappa x : ℝ) :
    kappa^2 * x^2 = (kappa*x)^2 := by ring

/-- The viscous linear term commutes with the amplitude rescaling. -/
theorem viscous_rescale (kappa nu N x : ℝ) :
    kappa * (-nu * N^2 * x) = -nu * N^2 * (kappa*x) := by ring

#print axioms quadratic_rescale_pair
#print axioms quadratic_rescale_square
#print axioms viscous_rescale

end NSFixedCoefficientRescaling
