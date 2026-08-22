import Mathlib

/-!
# Round 210 CM-density and Hilbert-polynomial finite firewalls

This file formalizes only abstract predicates and elementary polynomial/degree
arithmetic. It does not formalize Shimura varieties, CM points, weakly special
subvarieties, projective curves, Hilbert schemes, o-minimality, or the Hodge
conjecture.
-/

namespace Millennium
namespace Round210Hodge

/-- In a product notion of special point, the fibre over a non-special first
coordinate contains no special point. -/
theorem nonspecial_fibre_has_no_product_special
    {X Y : Type*}
    (SpecialX : X → Prop) (SpecialY : Y → Prop)
    (x : X) (hx : ¬ SpecialX x) :
    ¬ ∃ y : Y, SpecialX x ∧ SpecialY y := by
  intro h
  rcases h with ⟨y, hxy⟩
  exact hx hxy.1

/-- Hilbert polynomial of the scalar twisted-cubic model. -/
def twistedCubicHilbert (n : ℤ) : ℤ := 3 * n + 1

/-- Hilbert polynomial of the scalar smooth-plane-cubic model. -/
def planeCubicHilbert (n : ℤ) : ℤ := 3 * n

/-- The two models have the same degree/leading coefficient. -/
theorem cubic_hilbert_same_linear_coefficient (n : ℤ) :
    twistedCubicHilbert n - planeCubicHilbert n = 1 := by
  simp [twistedCubicHilbert, planeCubicHilbert]

/-- Equal degree does not force equal Hilbert polynomial. -/
theorem cubic_hilbert_polynomials_differ :
    twistedCubicHilbert ≠ planeCubicHilbert := by
  intro heq
  have hzero := congrFun heq 0
  norm_num [twistedCubicHilbert, planeCubicHilbert] at hzero

/-- Adding the same effective padding to positive and negative degrees preserves
their difference. -/
theorem common_effective_padding_preserves_difference
    (positive negative padding : ℕ) :
    (positive + padding) - (negative + padding) = positive - negative := by
  omega

/-- A fixed zero difference admits positive and negative degrees above every
prescribed bound, so the difference alone supplies no individual degree bound. -/
theorem fixed_difference_does_not_bound_both_effective_parts
    (bound : ℕ) :
    ∃ positive negative : ℕ,
      positive - negative = 0 ∧ bound ≤ positive ∧ bound ≤ negative := by
  exact ⟨bound, bound, by simp, le_rfl, le_rfl⟩

#print axioms nonspecial_fibre_has_no_product_special
#print axioms cubic_hilbert_same_linear_coefficient
#print axioms cubic_hilbert_polynomials_differ
#print axioms common_effective_padding_preserves_difference
#print axioms fixed_difference_does_not_bound_both_effective_parts

end Round210Hodge
end Millennium
