import Mathlib

/-!
# Inverse-free real-inner-product-space completed square

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
  ⟪D x, x⟫_ℝ - 2 * ⟪b, x⟫_ℝ

/-- Exact completed square with the residual `D z - b` left visible. -/
theorem quadratic_sub_with_residual
    (D : H →L[ℝ] H)
    (hD : (D : H →ₗ[ℝ] H).IsSymmetric)
    (b z y : H) :
    quadratic D b y - quadratic D b z =
      ⟪D (y - z), y - z⟫_ℝ + 2 * ⟪D z - b, y - z⟫_ℝ := by
  have hcross : ⟪D y, z⟫_ℝ = ⟪D z, y⟫_ℝ := by
    calc
      ⟪D y, z⟫_ℝ = ⟪y, D z⟫_ℝ := hD y z
      _ = ⟪D z, y⟫_ℝ := real_inner_comm (D z) y
  simp only [quadratic, D.map_sub, inner_sub_left, inner_sub_right, hcross]
  ring

/-- Inverse-free completed-square identity.  Only symmetry of `D` and an
explicit solution of `D z = b` are used; no inverse or coercivity is assumed. -/
theorem quadratic_sub_at_solution
    (D : H →L[ℝ] H)
    (hD : (D : H →ₗ[ℝ] H).IsSymmetric)
    (b z y : H)
    (hz : D z = b) :
    quadratic D b y - quadratic D b z = ⟪D (y - z), y - z⟫_ℝ := by
  have hcross : ⟪D y, z⟫_ℝ = ⟪b, y⟫_ℝ := by
    calc
      ⟪D y, z⟫_ℝ = ⟪y, D z⟫_ℝ := hD y z
      _ = ⟪y, b⟫_ℝ := by rw [hz]
      _ = ⟪b, y⟫_ℝ := real_inner_comm b y
  simp only [quadratic, D.map_sub, inner_sub_left, inner_sub_right, hz, hcross]
  ring

/-- If the symmetric quadratic part is nonnegative, any exact solution of
`D z = b` is a global minimizer of the quadratic functional. -/
theorem quadratic_minimum_at_solution
    (D : H →L[ℝ] H)
    (hD : (D : H →ₗ[ℝ] H).IsSymmetric)
    (hD_nonneg : ∀ x : H, 0 ≤ ⟪D x, x⟫_ℝ)
    (b z y : H)
    (hz : D z = b) :
    quadratic D b z ≤ quadratic D b y := by
  rw [← sub_nonneg, quadratic_sub_at_solution D hD b z y hz]
  exact hD_nonneg (y - z)

/-- Coercivity converts the visible residual into the exact squared penalty.
No inverse or exact solve is needed, but the positive constant `μ` is an
explicit load-bearing hypothesis. -/
theorem quadratic_lower_bound_of_coercive
    (D : H →L[ℝ] H)
    (hD : (D : H →ₗ[ℝ] H).IsSymmetric)
    (μ : ℝ)
    (hμ : 0 < μ)
    (hcoercive : ∀ x : H, μ * ‖x‖ ^ 2 ≤ ⟪D x, x⟫_ℝ)
    (b z y : H) :
    -(‖D z - b‖ ^ 2 / μ) ≤ quadratic D b y - quadratic D b z := by
  rw [quadratic_sub_with_residual D hD b z y]
  have hcs : -(‖D z - b‖ * ‖y - z‖) ≤ ⟪D z - b, y - z⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm (D z - b) (y - z))
  have hyoung : -(‖D z - b‖ ^ 2 / μ) ≤
      μ * ‖y - z‖ ^ 2 - 2 * ‖D z - b‖ * ‖y - z‖ := by
    have hdiv : -(‖D z - b‖ ^ 2) / μ ≤
        μ * ‖y - z‖ ^ 2 - 2 * ‖D z - b‖ * ‖y - z‖ := by
      apply (div_le_iff₀ hμ).2
      nlinarith [sq_nonneg (μ * ‖y - z‖ - ‖D z - b‖)]
    simpa only [neg_div] using hdiv
  have henergy := hcoercive (y - z)
  nlinarith

#print axioms quadratic_sub_with_residual
#print axioms quadratic_sub_at_solution
#print axioms quadratic_minimum_at_solution
#print axioms quadratic_lower_bound_of_coercive

end HilbertCompletedSquare
end RHBraid
