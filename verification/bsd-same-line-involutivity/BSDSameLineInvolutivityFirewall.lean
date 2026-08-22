import Mathlib

/-!
# BSD same-line involutivity firewall: finite algebraic core

HONESTY BOUNDARY

This file formalizes only the scalar algebra behind the distinction between
an involutive semilinear operator and a norm pairing on its vectors.  It also
checks the rank-one hyperbolic scaling countermodel.

It does not formalize determinant functors, derived categories, Selmer
complexes, Iwasawa algebras, the Burns--Sano or Macias Castillo--Sano maps,
Sano equation (5.4.4), elliptic curves, or BSD.
-/

namespace Millennium
namespace BSD
namespace SameLineInvolutivityFinite

/-- The coordinate model `F(x) = iota(x) * lambda` is involutive when the
operator multiplier has norm one. -/
theorem semilinear_model_involutive
    {A : Type*} [CommRing A]
    (iota : A →+* A) (hiota : Function.Involutive iota)
    (lambda : A) (hlambda : iota lambda * lambda = 1) :
    Function.Involutive (fun x : A => iota x * lambda) := by
  intro x
  simp only [map_mul, hiota x]
  calc
    (x * iota lambda) * lambda = x * (iota lambda * lambda) := by
      ac_rfl
    _ = x := by rw [hlambda, mul_one]

/-- Semilinearity under a change of generator. -/
theorem same_line_scale_rule
    {A : Type*} [CommRing A]
    (iota : A →+* A) (lambda u x : A) :
    iota (u * x) * lambda = iota u * (iota x * lambda) := by
  rw [map_mul]
  ac_rfl

/-- An involution-fixed change of generator preserves the same-line
functional-equation multiplier. -/
theorem fixed_scale_preserves_multiplier
    {A : Type*} [CommRing A]
    (iota : A →+* A) (lambda u : A)
    (hu : iota u = u) :
    iota u * lambda = lambda * u := by
  rw [hu]
  exact mul_comm u lambda

/-- The smallest countermodel: an involutive same-line map can give two
generators the same multiplier although their ratio is not norm one. -/
theorem rational_same_line_involutive_counterexample :
    let F : ℚ → ℚ := fun x => x
    Function.Involutive F ∧
      F 1 = 1 ∧
      F 2 = 2 ∧
      (2 : ℚ) * 2 ≠ 1 := by
  norm_num [Function.Involutive]

/-- The rank-one hyperbolic isometry scales one factor by `a` and its paired
dual factor by `aInv`. -/
theorem hyperbolic_pairing_preserved
    {A : Type*} [CommRing A]
    (a aInv x y : A) (hunit : a * aInv = 1) :
    (a * x) * (aInv * y) = x * y := by
  calc
    (a * x) * (aInv * y) = (a * aInv) * (x * y) := by ring
    _ = x * y := by rw [hunit, one_mul]

/-- On the odd hyperbolic determinant coordinate, the corresponding action
is multiplication by the involutive norm `a * iota(a)`. -/
theorem hyperbolic_orientation_norm_action
    {A : Type*} [CommRing A]
    (iota : A →+* A) (a x y : A) :
    (a * x) * (iota a * y) = (a * iota a) * (x * y) := by
  ring

/-- A concrete pairing-preserving hyperbolic change of basis whose
orientation norm is nontrivial. -/
theorem rational_hyperbolic_orientation_counterexample (x y : ℚ) :
    ((2 * x) * ((1 / 2) * y) = x * y) ∧
      (2 : ℚ) * 2 ≠ 1 := by
  constructor
  · ring
  · norm_num

#print axioms semilinear_model_involutive
#print axioms same_line_scale_rule
#print axioms fixed_scale_preserves_multiplier
#print axioms rational_same_line_involutive_counterexample
#print axioms hyperbolic_pairing_preserved
#print axioms hyperbolic_orientation_norm_action
#print axioms rational_hyperbolic_orientation_counterexample

end SameLineInvolutivityFinite
end BSD
end Millennium
