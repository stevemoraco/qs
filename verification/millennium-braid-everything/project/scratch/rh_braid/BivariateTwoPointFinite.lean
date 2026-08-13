import Mathlib

/-!
# Two-point finite witness for the bivariate exterior RH criterion

Finite algebra only.  This does not prove RH.

For a Hermitian 2x2 kernel matrix with diagonal `r` and off-diagonal
`z = x + i y`, the determinant is `r^2 - |z|^2`.  If `|z| > r`,
the determinant is negative, hence the matrix cannot be positive semidefinite.
-/

namespace RHProof
namespace BivariateTwoPoint

/-- The scalar determinant identity behind the two-point kernel test. -/
theorem det_scalar_identity (r x y : ℝ) :
    r * r - (x * x + y * y) = r^2 - x^2 - y^2 := by
  ring

/-- If the off-diagonal modulus squared exceeds the diagonal square,
then the 2x2 Hermitian determinant is strictly negative. -/
theorem negative_det_of_modsq_gt
    (r x y : ℝ)
    (h : r^2 < x^2 + y^2) :
    r^2 - (x^2 + y^2) < 0 := by
  linarith

/-- Pointwise violation of `|z| ≤ r` gives the finite negative determinant
certificate used by the bivariate exterior RH criterion. -/
theorem two_point_violation_certificate
    (r x y : ℝ)
    (hr : 0 ≤ r)
    (hmod : r < Real.sqrt (x^2 + y^2)) :
    r^2 - (x^2 + y^2) < 0 := by
  have hsq_nonneg : 0 ≤ x^2 + y^2 := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (x^2 + y^2) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (x^2 + y^2))^2 = x^2 + y^2 := by
    simpa using Real.sq_sqrt hsq_nonneg
  have hsq : r^2 < (Real.sqrt (x^2 + y^2))^2 := by
    nlinarith
  rw [hsqrt_sq] at hsq
  linarith

end BivariateTwoPoint
end RHProof
