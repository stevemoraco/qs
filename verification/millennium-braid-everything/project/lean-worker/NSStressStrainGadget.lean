import Mathlib

namespace NSStressStrainGadget

/-- Off-diagonal stress/strain contraction: the two symmetric xy entries give
exactly `-c U N C^2`. Here `C` stands for `cos(Ny)`. -/
theorem strain_contraction (c U N C : ℝ) :
    2 * (-c*C) * (U*N*C/2) = -c*U*N*C^2 := by
  ring

/-- The two xy-block eigenvalue candidates of `[[lambda,-cC],[-cC,lambda]]`
are `lambda-cC` and `lambda+cC`; their product is the determinant. -/
theorem xy_determinant_factor (lambda c C : ℝ) :
    lambda^2 - (c*C)^2 = (lambda-c*C)*(lambda+c*C) := by
  ring

/-- If |C|<=1 and lambda>c>0, then both xy-block eigenvalue candidates are positive. -/
theorem xy_eigenvalues_pos
    {lambda c C : ℝ}
    (hc : 0 < c)
    (hl : c < lambda)
    (hClo : -1 ≤ C)
    (hChi : C ≤ 1) :
    0 < lambda-c*C ∧ 0 < lambda+c*C := by
  constructor <;> nlinarith

/-- Negative strain work under positive parameters; strict away from a node C=0. -/
theorem strain_work_neg
    {c U N C : ℝ}
    (hc : 0 < c) (hU : 0 < U) (hN : 0 < N) (hC : C ≠ 0) :
    -c*U*N*C^2 < 0 := by
  have hC2 : 0 < C^2 := sq_pos_of_ne_zero hC
  positivity

/-- The shell strain scaling identity: U=N^(beta-1) gives N*U exponent beta. -/
theorem strain_exponent (beta : ℝ) :
    1 + (beta-1) = beta := by ring

/-- Palasek's amplifier coefficient has the same exponent because
`N^alpha X`, with `X` exponent beta-alpha, also has exponent beta. -/
theorem palasek_amplifier_exponent (alpha beta : ℝ) :
    alpha + (beta-alpha) = beta := by ring

#print axioms strain_contraction
#print axioms xy_determinant_factor
#print axioms xy_eigenvalues_pos
#print axioms strain_work_neg
#print axioms strain_exponent
#print axioms palasek_amplifier_exponent

end NSStressStrainGadget
