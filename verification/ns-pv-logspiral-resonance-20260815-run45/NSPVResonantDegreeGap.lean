import Mathlib

/-!
# Finite degree-gap firewall for the RSS log-spiral resonance

After choosing the logarithmic radial phase that cancels the angular rotation,
the first-order rotated self-similar operator on a formal `r^(-k)` mode leaves
only the scalar homogeneity eigenvalue `(1-k)/2`.

Thus degree `k=1` is critical/resonant, while degree `k=3` has eigenvalue `-1`.
This is the finite coefficient shadow of the observation that the Type-I
`r^(-1)` tail is resonant but the schematic `r^(-3)` diffusion/nonlinear
corrections are not resonant for the same first-order operator.

This file does NOT formalize powers of radius, logarithms, trigonometric modes,
asymptotic expansions, the Pineau--Vicol equation, or Navier--Stokes.
-/

namespace NSPVResonantDegreeGap

/-- Remaining homogeneity eigenvalue after the log-spiral phase cancels rotation. -/
def degreeEigenvalue (k : ℝ) : ℝ :=
  (1 - k) / 2

/-- Formal coefficient pair for one angular mode after including rotation,
logarithmic radial twist, and an `r^(-k)` homogeneity contribution. -/
def degreeModeOperator
    (alpha n k a b : ℝ) : ℝ × ℝ :=
  (alpha * (-n * b) + alpha * n * b + degreeEigenvalue k * a,
   alpha * (n * a) - alpha * n * a + degreeEigenvalue k * b)

/-- Rotation and log-radial phase cancel, leaving only the degree eigenvalue. -/
theorem degree_mode_reduction
    (alpha n k a b : ℝ) :
    degreeModeOperator alpha n k a b =
      (degreeEigenvalue k * a, degreeEigenvalue k * b) := by
  ext <;> simp [degreeModeOperator, degreeEigenvalue] <;> ring

/-- The critical `r^-1` degree is exactly resonant. -/
theorem critical_degree_one_kernel
    (alpha n a b : ℝ) :
    degreeModeOperator alpha n 1 a b = (0, 0) := by
  simp [degree_mode_reduction, degreeEigenvalue]

/-- The schematic `r^-3` correction degree has eigenvalue exactly `-1`. -/
theorem cubic_degree_three_minus_identity
    (alpha n a b : ℝ) :
    degreeModeOperator alpha n 3 a b = (-a, -b) := by
  rw [degree_mode_reduction]
  norm_num [degreeEigenvalue]

/-- At degree three the squared coefficient activity is exactly the original
squared amplitude, so this sector has no first-order resonance. -/
theorem cubic_degree_three_activity
    (alpha n a b : ℝ) :
    (degreeModeOperator alpha n 3 a b).1 ^ 2 +
      (degreeModeOperator alpha n 3 a b).2 ^ 2 =
      a ^ 2 + b ^ 2 := by
  rw [cubic_degree_three_minus_identity]
  ring

/-- Critical and cubic homogeneities have different first-order eigenvalues. -/
theorem critical_cubic_eigenvalue_gap :
    degreeEigenvalue 1 = 0 ∧ degreeEigenvalue 3 = -1 := by
  norm_num [degreeEigenvalue]

#print axioms degree_mode_reduction
#print axioms critical_degree_one_kernel
#print axioms cubic_degree_three_minus_identity
#print axioms cubic_degree_three_activity
#print axioms critical_cubic_eigenvalue_gap

end NSPVResonantDegreeGap
