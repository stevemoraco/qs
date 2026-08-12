import Mathlib

/-!
# BSD augmentation-localization blindness: finite algebraic core

This file formalizes only the abstract algebra used in the accompanying source
audit:

* if a distinguished element becomes a unit after a monoid/ring map, multiplying
  by any power of it does not change the associated class;
* a positive integral order shift is nevertheless nonzero;
* separately imposed valuation lower bounds merge through `max`, while their
  additive sum is strictly larger when both local defects are positive.

It does not formalize Iwasawa algebras, height-one primes, localization at the
augmentation ideal, determinant lines, Kato's zeta element, dual exponentials,
elliptic curves, Tamagawa factors, or BSD.
-/

namespace MillenniumBraid
namespace BSDAugmentationBlindness

variable {R S : Type*}
variable [CommMonoid R] [CommMonoid S]

/-- Once the image of `π` is a unit, an arbitrary `π^a` multiple has the same
associated class after mapping. -/
theorem power_multiple_associated_after_map
    (f : R →* S) (π x : R) (a : ℕ)
    (hπ : IsUnit (f π)) :
    Associated (f (π ^ a * x)) (f x) := by
  rw [map_mul, map_pow]
  exact associated_unit_mul_left (f x) ((f π) ^ a) (hπ.pow a)

/-- The reverse orientation is available as well. -/
theorem original_associated_power_multiple_after_map
    (f : R →* S) (π x : R) (a : ℕ)
    (hπ : IsUnit (f π)) :
    Associated (f x) (f (π ^ a * x)) := by
  exact (power_multiple_associated_after_map f π x a hπ).symm

/-- An integral order shifted by a positive exponent cannot remain unchanged. -/
theorem positive_integral_shift_changes_order
    (a v : ℕ) (ha : 0 < a) :
    a + v ≠ v := by
  omega

/-- The only way an additive nonnegative order shift is invisible is for the
shift itself to be zero. -/
theorem integral_shift_eq_iff
    (a v : ℕ) :
    a + v = v ↔ a = 0 := by
  omega

/-- Separate lower bounds combine into the maximum exponent. -/
theorem separate_bounds_give_max
    (a b c : ℕ) (ha : a ≤ c) (hb : b ≤ c) :
    max a b ≤ c := by
  exact max_le ha hb

/-- When two local defects are positive, their required additive total is
strictly larger than the scalar maximum retained by one divisibility chain. -/
theorem max_strictly_below_sum
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    max a b < a + b := by
  omega

/-- Concrete divisibility shadow: one exponent can satisfy two identical local
requirements while failing their sum. -/
theorem two_local_factors_do_not_add_in_one_chain :
    (2 : ℕ) ∣ 2 ∧ (2 : ℕ) ∣ 2 ∧ ¬ (4 : ℕ) ∣ 2 := by
  norm_num

#print axioms power_multiple_associated_after_map
#print axioms original_associated_power_multiple_after_map
#print axioms positive_integral_shift_changes_order
#print axioms integral_shift_eq_iff
#print axioms separate_bounds_give_max
#print axioms max_strictly_below_sum
#print axioms two_local_factors_do_not_add_in_one_chain

end BSDAugmentationBlindness
end MillenniumBraid
