import Mathlib

/-!
# Round 210 product Hodge-type finite countermodel

This file formalizes only bidegree addition. It does not formalize Hodge
structures, rationality, Künneth decompositions, algebraic correspondences,
products of varieties, or the Hodge conjecture.
-/

namespace Millennium
namespace Round210Hodge

abbrev HodgeType := ℤ × ℤ

/-- A scalar Hodge type is diagonal when its two bidegrees agree. -/
def IsDiagonalType (pq : HodgeType) : Prop := pq.1 = pq.2

/-- Tensor products add the two Hodge bidegrees componentwise. -/
def tensorType (pq rs : HodgeType) : HodgeType :=
  (pq.1 + rs.1, pq.2 + rs.2)

/-- A `(1,0)` factor is not itself diagonal. -/
theorem left_cross_factor_not_diagonal :
    ¬ IsDiagonalType ((1, 0) : HodgeType) := by
  norm_num [IsDiagonalType]

/-- A `(0,1)` factor is not itself diagonal. -/
theorem right_cross_factor_not_diagonal :
    ¬ IsDiagonalType ((0, 1) : HodgeType) := by
  norm_num [IsDiagonalType]

/-- Their tensor bidegree is `(1,1)`, hence diagonal. -/
theorem cross_tensor_is_diagonal :
    IsDiagonalType
      (tensorType ((1, 0) : HodgeType) ((0, 1) : HodgeType)) := by
  norm_num [IsDiagonalType, tensorType]

/-- Exact logical countermodel to the claim that a diagonal tensor type forces
both factor types to be diagonal. -/
theorem diagonal_tensor_does_not_force_diagonal_factors :
    ∃ (pq rs : HodgeType),
      IsDiagonalType (tensorType pq rs) ∧
      ¬ IsDiagonalType pq ∧ ¬ IsDiagonalType rs := by
  exact ⟨(1, 0), (0, 1), cross_tensor_is_diagonal,
    left_cross_factor_not_diagonal, right_cross_factor_not_diagonal⟩

#print axioms left_cross_factor_not_diagonal
#print axioms right_cross_factor_not_diagonal
#print axioms cross_tensor_is_diagonal
#print axioms diagonal_tensor_does_not_force_diagonal_factors

end Round210Hodge
end Millennium
