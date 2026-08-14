import Mathlib

namespace Millennium.Hodge.BasketBTypeIDVRIndexFiniteCore

open Matrix

theorem gram_det_is_det_square
    {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) :
    (M.transpose * M).det = M.det ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_transpose]
  ring

theorem index_two_or_three
    (δ d : ℕ)
    (hδ : 2 ≤ δ)
    (hdisc : d = 2 * δ)
    (hbudget : d ≤ 6) :
    δ = 2 ∨ δ = 3 := by
  omega

theorem discriminant_four_or_six
    (δ d : ℕ)
    (hδ : 2 ≤ δ)
    (hdisc : d = 2 * δ)
    (hbudget : d ≤ 6) :
    d = 4 ∨ d = 6 := by
  rcases index_two_or_three δ d hδ hdisc hbudget with rfl | rfl <;> omega

#print axioms gram_det_is_det_square
#print axioms index_two_or_three
#print axioms discriminant_four_or_six

end Millennium.Hodge.BasketBTypeIDVRIndexFiniteCore
