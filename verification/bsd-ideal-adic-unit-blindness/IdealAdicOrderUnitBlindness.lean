import Mathlib

/-!
# BSD finite algebra: ideal-adic order is generator-independent

The official Clay BSD statement asks for the order of vanishing, not the refined
leading coefficient. This file proves the finite algebraic core showing that
principal-unit ambiguity does not obstruct an order defined through containment
in powers of a distinguished ideal.

This does not formalize Iwasawa theory or prove BSD.
-/

namespace BSDProof
namespace IdealAdicOrderUnitBlindness

/-- Multiplication by a unit does not change a principal ideal. -/
theorem principal_ideal_unit_blind
    {R : Type*} [Semiring R]
    (u x : R) (hu : IsUnit u) :
    Ideal.span ({u * x} : Set R) = Ideal.span ({x} : Set R) := by
  exact Ideal.span_singleton_mul_left_unit hu x

/-- Every containment test in a power of a distinguished ideal is blind to a
unit change of principal generator. -/
theorem power_containment_unit_blind
    {R : Type*} [CommSemiring R]
    (P : Ideal R) (u x : R) (hu : IsUnit u) (n : ℕ) :
    (Ideal.span ({u * x} : Set R) ≤ P ^ n) ↔
      (Ideal.span ({x} : Set R) ≤ P ^ n) := by
  rw [principal_ideal_unit_blind u x hu]

/-- Equal principal ideals have identical containment depth in every power of
any chosen ideal. -/
theorem equal_principal_ideals_same_power_containment
    {R : Type*} [CommSemiring R]
    (P : Ideal R) {x y : R}
    (hxy : Ideal.span ({x} : Set R) = Ideal.span ({y} : Set R))
    (n : ℕ) :
    (Ideal.span ({x} : Set R) ≤ P ^ n) ↔
      (Ideal.span ({y} : Set R) ≤ P ^ n) := by
  rw [hxy]

#print axioms principal_ideal_unit_blind
#print axioms power_containment_unit_blind
#print axioms equal_principal_ideals_same_power_containment

end IdealAdicOrderUnitBlindness
end BSDProof
