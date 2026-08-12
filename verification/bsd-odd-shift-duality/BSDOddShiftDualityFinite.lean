import Mathlib

/-!
# BSD odd-shift duality firewall: finite algebraic core

HONESTY BOUNDARY

This file verifies only finite/scalar algebra used in the accompanying BSD
source audit:

* invariance plus norm one implies square one;
* square one in a domain implies the two possible signs;
* a specialization removes the negative sign only when it separates `-1`
  from `1`;
* reduction modulo two does not separate the signs;
* a concrete truncated-polynomial involution has a nontrivial invariant unit
  of augmentation one whose involutive norm is not one.

It does not formalize determinant functors, derived categories, Selmer
complexes, Iwasawa algebras, Artin--Verdier duality, leading terms, BSD, or any
Millennium theorem.
-/

namespace Millennium
namespace BSD
namespace OddShiftDualityFinite

/-- The scalar core of the double-symmetry argument. -/
theorem invariant_norm_one_implies_square_one
    {A : Type*} [Monoid A]
    (iota : A → A) (u : A)
    (hfix : iota u = u)
    (hnorm : u * iota u = 1) :
    u ^ 2 = 1 := by
  rw [hfix] at hnorm
  simpa [pow_two] using hnorm

/-- In a commutative domain, a square root of one is one of the two signs. -/
theorem square_one_implies_sign
    {A : Type*} [CommRing A] [IsDomain A]
    (u : A) (hsq : u ^ 2 = 1) :
    u = 1 ∨ u = -1 := by
  have hprod : (u - 1) * (u + 1) = 0 := by
    calc
      (u - 1) * (u + 1) = u ^ 2 - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  rcases mul_eq_zero.mp hprod with hleft | hright
  · left
    exact sub_eq_zero.mp hleft
  · right
    calc
      u = u + 1 - 1 := by ring
      _ = 0 - 1 := by rw [hright]
      _ = -1 := by ring

/-- A sign-separating specialization removes the negative possibility. -/
theorem sign_separating_specialization
    {A B : Type*} [Ring A] [Ring B]
    (phi : A →+* B) (u : A)
    (hsign : u = 1 ∨ u = -1)
    (hphi : phi u = 1)
    (hseparate : phi (-1) ≠ 1) :
    u = 1 := by
  rcases hsign with hone | hneg
  · exact hone
  · exfalso
    apply hseparate
    rw [← hneg, hphi]

/-- Modulo two, `-1` specializes to `1`, so this specialization cannot select
    the positive sign. -/
theorem modulo_two_does_not_separate_sign :
    (-1 : ℤ) ≠ 1 ∧ (((-1 : ℤ) : ZMod 2) = 1) := by
  constructor
  · norm_num
  · decide

/-- Concrete determinant parity exponents for shifts three and two. -/
theorem shift_three_has_same_line_polarity :
    (-1 : ℤ) ^ (3 + 1) = 1 := by
  norm_num

theorem shift_two_has_inverse_line_polarity :
    (-1 : ℤ) ^ (2 + 1) = -1 := by
  norm_num

/-- Coefficients of `F_5[epsilon]/(epsilon^3)`. -/
@[ext]
structure Trunc3 where
  c0 : ZMod 5
  c1 : ZMod 5
  c2 : ZMod 5
  deriving DecidableEq, Repr

def tOne : Trunc3 := ⟨1, 0, 0⟩

def tMul (x y : Trunc3) : Trunc3 :=
  ⟨x.c0 * y.c0,
   x.c0 * y.c1 + x.c1 * y.c0,
   x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0⟩

/-- The involution `epsilon ↦ -epsilon`. -/
def tIota (x : Trunc3) : Trunc3 :=
  ⟨x.c0, -x.c1, x.c2⟩

def tAug (x : Trunc3) : ZMod 5 := x.c0

/-- `1 + epsilon^2`. -/
def tUnit : Trunc3 := ⟨1, 0, 1⟩

/-- `1 - epsilon^2`, the inverse of `tUnit`. -/
def tUnitInv : Trunc3 := ⟨1, 0, -1⟩

theorem tIota_involutive (x : Trunc3) :
    tIota (tIota x) = x := by
  rcases x with ⟨a, b, c⟩
  simp [tIota]

theorem tIota_multiplicative (x y : Trunc3) :
    tIota (tMul x y) = tMul (tIota x) (tIota y) := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  ext <;> simp [tIota, tMul] <;> ring

theorem tUnit_has_inverse :
    tMul tUnit tUnitInv = tOne := by
  decide

theorem invariant_augmented_unit_without_norm :
    tIota tUnit = tUnit ∧
    tAug tUnit = 1 ∧
    tUnit ≠ tOne ∧
    tMul tUnit (tIota tUnit) ≠ tOne := by
  decide

#print axioms invariant_norm_one_implies_square_one
#print axioms square_one_implies_sign
#print axioms sign_separating_specialization
#print axioms modulo_two_does_not_separate_sign
#print axioms shift_three_has_same_line_polarity
#print axioms shift_two_has_inverse_line_polarity
#print axioms tIota_involutive
#print axioms tIota_multiplicative
#print axioms tUnit_has_inverse
#print axioms invariant_augmented_unit_without_norm

end OddShiftDualityFinite
end BSD
end Millennium
