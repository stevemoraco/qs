import Mathlib

/-!
# BSD regulator index-square finite core

This file formalizes the matrix identity behind regulator scaling under a
full-rank change of lattice and the parity obstruction it imposes on any
attempt to repair a p-adic BSD discrepancy solely by Mordell--Weil
saturation.

It does not formalize elliptic curves, Neron--Tate heights, Mordell--Weil
lattices, valuations, Selmer groups, or the Birch--Swinnerton-Dyer
conjecture.
-/

namespace MillenniumBSD
namespace RegulatorIndexSquare

open Matrix

/-- The Gram determinant changes by the square of the determinant of the
change-of-basis matrix. -/
theorem det_transpose_mul_mul
    {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n R) :
    (A.transpose * H * A).det = A.det ^ 2 * H.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The same identity with the square written as an explicit product. -/
theorem det_transpose_mul_mul_explicit
    {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n R) :
    (A.transpose * H * A).det = A.det * A.det * H.det := by
  rw [det_transpose_mul_mul]
  ring

/-- Every abstract valuation contribution of an index square is even. -/
theorem twice_is_even (s : ℤ) : Even (2 * s) := by
  exact ⟨s, by ring⟩

/-- An odd residual valuation discrepancy cannot equal a regulator
saturation correction `2*s`. -/
theorem odd_discrepancy_ne_twice
    (delta s : ℤ) (hdelta : Odd delta) :
    delta ≠ 2 * s := by
  rintro rfl
  rcases hdelta with ⟨k, hk⟩
  omega

/-- If a discrepancy is known to be both an index-square correction and odd,
the hypotheses are inconsistent. -/
theorem no_odd_saturation_repair
    (delta s : ℤ)
    (hsaturation : delta = 2 * s)
    (hodd : Odd delta) : False := by
  exact odd_discrepancy_ne_twice delta s hodd hsaturation

/-- A certified saturation bound `0 ≤ s ≤ B` restricts the correction to
the even interval from `0` through `2B`. -/
theorem bounded_saturation_budget
    (B s correction : ℕ)
    (hs_nonneg : 0 ≤ s)
    (hs_bound : s ≤ B)
    (hcorrection : correction = 2 * s) :
    correction ≤ 2 * B ∧ Even correction := by
  constructor
  · omega
  · exact ⟨s, by omega⟩

#print axioms det_transpose_mul_mul
#print axioms det_transpose_mul_mul_explicit
#print axioms twice_is_even
#print axioms odd_discrepancy_ne_twice
#print axioms no_odd_saturation_repair
#print axioms bounded_saturation_budget

end RegulatorIndexSquare
end MillenniumBSD
