import Mathlib

/-!
# Finite core for surjective pullback negative-index bookkeeping

These lemmas deliberately avoid defining a global inertia API. They prove the two
finite facts used by the paper theorem:

* strict negativity of a pullback forces the evaluation map to be injective on
  the negative subspace;
* a right inverse lifts strict negativity exactly.

No statement about zeta or RH is encoded here.
-/

namespace RHProof
namespace SurjectiveNegativeIndexCore

/-- Kernel fact: no nonzero vector can map to zero under a strictly negative
pullback when `q 0 = 0`. -/
theorem eq_zero_of_mapsToZero_under_strict_negative
    {A B : Type*} [Zero A] [Zero B]
    (E : A → B) (q : B → ℝ)
    (hq0 : q 0 = 0)
    (hneg : ∀ x : A, x ≠ 0 → q (E x) < 0)
    {x : A} (hx : E x = 0) :
    x = 0 := by
  by_contra hxn
  have hlt : q (E x) < 0 := hneg x hxn
  rw [hx, hq0] at hlt
  exact (lt_irrefl 0) hlt

/-- Additive/linear core: strict negativity on every nonzero vector forces an
additive evaluation map to be injective. In the inertia application the domain
is the subtype of a negative linear subspace. -/
theorem injective_of_strict_negative_pullback
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A →+ B) (q : B → ℝ)
    (hq0 : q 0 = 0)
    (hneg : ∀ x : A, x ≠ 0 → q (E x) < 0) :
    Function.Injective E := by
  intro x y hxy
  have hz : E (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hsub : x - y = 0 :=
    eq_zero_of_mapsToZero_under_strict_negative E q hq0 hneg hz
  exact sub_eq_zero.mp hsub

/-- A right inverse transports a negative vector upstairs without changing its
quadratic value. -/
theorem rightInverse_lifts_negative
    {A B : Type*}
    (E : A → B) (s : B → A) (q : B → ℝ)
    (hsec : ∀ y : B, E (s y) = y)
    {y : B} (hy : q y < 0) :
    q (E (s y)) < 0 := by
  simpa [hsec y] using hy

/-- Pointwise version for an entire negative family. -/
theorem rightInverse_lifts_strict_negative_family
    {A B : Type*} [Zero B]
    (E : A → B) (s : B → A) (q : B → ℝ)
    (hsec : ∀ y : B, E (s y) = y)
    (hneg : ∀ y : B, y ≠ 0 → q y < 0) :
    ∀ y : B, y ≠ 0 → q (E (s y)) < 0 := by
  intro y hy
  simpa [hsec y] using hneg y hy

end SurjectiveNegativeIndexCore
end RHProof
