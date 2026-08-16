import Mathlib

/-!
# Hodge C114 negative-determinant family: finite scalar core

This file formalizes only the integer identities behind the explicit infinite
family discovered in the product-eight hostile audit.  It does not formalize
Neron--Severi lattices, nef cones, positive-semidefinite matrices, finite
covers, Casnati--Ekedahl geometry, Hodge theory, or a Clay theorem.
-/

namespace Millennium.Hodge.Bidegree24NegativeFamilyScalar

/-- The proposed negative determinant vector has square `-8r` in the
`(e,h)` Gram form `2xy+2y^2`. -/
theorem d2_square_identity (r : ℤ) :
    2 * (-2 * r - 2) * (2 * r) + 2 * (2 * r) ^ 2 = -8 * r := by
  ring

/-- The explicit matrix-family trace exactly matches the C113 trace formula
`10 - 2 D2^2`. -/
theorem trace_matches_negative_square (r : ℤ) :
    10 + 16 * r = 10 - 2 * (-8 * r) := by
  ring

/-- Determinant of the two-by-two defect matrix in the explicit family. -/
theorem defect_determinant_identity (r : ℤ) :
    (8 * r + 4) * (32 * r + 4) - (16 * r + 1) ^ 2 =
      128 * r + 15 := by
  ring

/-- For positive integral family parameter the defect determinant is strictly
positive. -/
theorem defect_determinant_positive (r : ℕ) :
    (0 : ℤ) < 128 * (r : ℤ) + 15 := by
  positivity

/-- Both diagonal entries of the defect matrix are positive. -/
theorem defect_diagonal_positive (r : ℕ) :
    (0 : ℤ) < 8 * (r : ℤ) + 4 ∧
    (0 : ℤ) < 32 * (r : ℤ) + 4 := by
  constructor <;> positivity

/-- The second coordinate of the boundary action is exactly even. -/
theorem boundary_second_coordinate_even (r : ℤ) :
    8 * r ^ 2 + 4 * r - 2 = 2 * (4 * r ^ 2 + 2 * r - 1) := by
  ring

/-- The displayed matrix action on the determinant vector gives the claimed
boundary coordinate before division by two. -/
theorem boundary_action_second_identity (r : ℤ) :
    (-2 * r - 2) + (4 * r + 3) * (2 * r) =
      8 * r ^ 2 + 4 * r - 2 := by
  ring

#print axioms d2_square_identity
#print axioms trace_matches_negative_square
#print axioms defect_determinant_identity
#print axioms defect_determinant_positive
#print axioms defect_diagonal_positive
#print axioms boundary_second_coordinate_even
#print axioms boundary_action_second_identity

end Millennium.Hodge.Bidegree24NegativeFamilyScalar
