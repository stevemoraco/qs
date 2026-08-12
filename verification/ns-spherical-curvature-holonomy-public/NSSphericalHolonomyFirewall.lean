import Mathlib

namespace NSSphericalHolonomy

open Matrix

/-- The standard basis vectors of `ℝ³`, written as finite coordinate vectors. -/
def e0 : Fin 3 → ℝ := ![1, 0, 0]
def e1 : Fin 3 → ℝ := ![0, 1, 0]
def e2 : Fin 3 → ℝ := ![0, 0, 1]

/-- Right-angle orthogonal transport from the `e0` normal to the `e1` normal. -/
def R01 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -1, 0;
     1,  0, 0;
     0,  0, 1]

/-- Right-angle orthogonal transport from the `e1` normal to the `e2` normal. -/
def R12 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0,  0;
     0, 0, -1;
     0, 1,  0]

/-- Right-angle orthogonal transport from the `e2` normal back to the `e0` normal. -/
def R20 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ 0, 0, 1;
      0, 1, 0;
     -1, 0, 0]

/-- Each edge matrix sends the indicated normal to the next normal. -/
theorem right_angle_transports_map_normals :
    R01 *ᵥ e0 = e1 ∧ R12 *ᵥ e1 = e2 ∧ R20 *ᵥ e2 = e0 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [R01, e0, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · constructor
    · ext i
      fin_cases i <;> norm_num [R12, e1, e2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · ext i
      fin_cases i <;> norm_num [R20, e2, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The three edge transports are orthogonal matrices. -/
theorem right_angle_transports_are_orthogonal :
    R01.transpose * R01 = 1 ∧
    R12.transpose * R12 = 1 ∧
    R20.transpose * R20 = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R01, Matrix.mul_apply, Fin.sum_univ_succ]
  · constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [R12, Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [R20, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Exact holonomy of the coordinate spherical right triangle: transport along
`e0 → e1 → e2 → e0` returns with a quarter turn in the tangent plane at `e0`.
The product is `R12`, not the identity. -/
theorem coordinate_right_triangle_holonomy :
    R20 * R12 * R01 = R12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R01, R12, R20, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The right-triangle holonomy fixes the base normal and rotates its tangent
basis by a quarter turn. -/
theorem coordinate_right_triangle_holonomy_action :
    (R20 * R12 * R01) *ᵥ e0 = e0 ∧
    (R20 * R12 * R01) *ᵥ e1 = e2 ∧
    (R20 * R12 * R01) *ᵥ e2 = -e1 := by
  rw [coordinate_right_triangle_holonomy]
  constructor
  · ext i
    fin_cases i <;> norm_num [R12, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · constructor
    · ext i
      fin_cases i <;> norm_num [R12, e1, e2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · ext i
      fin_cases i <;> norm_num [R12, e2, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Consequently the canonical edge transports around this spherical triangle
do not form a flat vertex-frame coboundary. -/
theorem coordinate_right_triangle_holonomy_nontrivial :
    R20 * R12 * R01 ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [coordinate_right_triangle_holonomy]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) h
  norm_num [R12] at hentry

/-- Subtracting the geometric transport leaves the identity defect in this
purely geometric example.  This is the finite algebraic model for replacing raw
holonomy by curvature-relative holonomy. -/
theorem curvature_subtracted_holonomy_is_trivial :
    (R20 * R12 * R01) * R12.transpose = 1 := by
  rw [coordinate_right_triangle_holonomy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R12, Matrix.mul_apply, Fin.sum_univ_succ]

#print axioms right_angle_transports_map_normals
#print axioms right_angle_transports_are_orthogonal
#print axioms coordinate_right_triangle_holonomy
#print axioms coordinate_right_triangle_holonomy_action
#print axioms coordinate_right_triangle_holonomy_nontrivial
#print axioms curvature_subtracted_holonomy_is_trivial

end NSSphericalHolonomy
