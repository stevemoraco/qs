import Mathlib

/-!
# BSD finite algebra: ideal-valued statements are unit-blind

This file formalizes the elementary algebraic obstruction used in the BSD braid.
It does not prove BSD.

An equality of principal ideals identifies generators only up to association
(i.e. multiplication by a unit), and multiplying a generator by a unit leaves
its principal ideal unchanged.
-/

namespace BSDProof
namespace UnitBlindness

/-- Multiplying a generator by a unit leaves its principal ideal unchanged. -/
theorem principal_ideal_unit_blind
    {R : Type*} [Semiring R]
    (u x : R) (hu : IsUnit u) :
    Ideal.span ({u * x} : Set R) = Ideal.span ({x} : Set R) := by
  exact Ideal.span_singleton_mul_left_unit hu x

/-- Over a domain, equality of principal ideals says exactly that the two
    generators are associated, hence differ by a unit. -/
theorem principal_ideal_equality_iff_associated
    {R : Type*} [CommSemiring R] [IsDomain R]
    {x y : R} :
    Ideal.span ({x} : Set R) = Ideal.span ({y} : Set R) ↔ Associated x y := by
  exact Ideal.span_singleton_eq_span_singleton

end UnitBlindness
end BSDProof
