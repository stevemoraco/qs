import Mathlib

/-!
# Inverse-free Hilbert-space completed square

This is the abstract real-Hilbert-space algebra behind a Schur/Feshbach
minimization step.  It does not construct the operator, solve `D z = b`, prove
positivity of `D`, define the Weil form, or imply the Riemann hypothesis.
-/

namespace RHBraid
namespace HilbertCompletedSquare

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The quadratic functional associated to `D` and the linear term `b`. -/
def quadratic (D : H →L[ℝ] H) (b x : H) : ℝ :=
  ⟨D x, x⟩_ℝ - 2 * ⟨b, x⟩_ℝ

/-- Inverse-free completed-square identity.  Only symmetry of `D` and an
explicit solution of `D z = b` are used; no inverse or coercivity is assumed. -/
theorem quadratic_sub_at_solution
    (D : H →L[ℝ] H)
    (hD : (D : H →ₗ[ℝ] H).IsSymmetric)
    (b z y : H)
    (hz : D z = b) :
    quadratic D b y - quadratic D b z = ⟨D (y - z), y - z⟩_ℝ := by
  have hcross : ⟨D y, z⟩_ℝ = ⟨b, y⟩_ℝ := by
    calc
      ⟨D y, z⟩_ℝ = ⟨y, D z⟩_ℝ := hD y z
      _ = ⟨y, b⟩_ℝ := by rw [hz]
      _ = ⟨b, y⟩_ℝ := real_inner_comm b y
  simp only [quadratic, D.map_sub, inner_sub_left, inner_sub_right, hz, hcross]
  ring

/-- If the symmetric quadratic part is nonnegative, any exact solution of
`D z = b` is a global minimizer of the quadratic functional. -/
theorem quadratic_minimum_at_solution
    (D : H →L[ℝ] H)
    (hD : (D : H →ₗ[ℝ] H).IsSymmetric)
    (hD_nonneg : ∀ x : H, 0 ≤ ⟨D x, x⟩_ℝ)
    (b z y : H)
    (hz : D z = b) :
    quadratic D b z ≤ quadratic D b y := by
  rw [← sub_nonneg, quadratic_sub_at_solution D hD b z y hz]
  exact hD_nonneg (y - z)

#print axioms quadratic_sub_at_solution
#print axioms quadratic_minimum_at_solution

end HilbertCompletedSquare
end RHBraid
