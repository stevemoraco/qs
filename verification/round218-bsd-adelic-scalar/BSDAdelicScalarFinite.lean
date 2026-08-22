import Mathlib

/-!
# Round 218 BSD adelic-scalar finite cores

This file formalizes only elementary scalar uniqueness, divisibility, sign,
and finite local-unit facts. It does not formalize elliptic curves, L-functions,
Selmer complexes, determinant functors, regulators, Tate--Shafarevich groups,
Tamagawa factors, p-adic valuations, or Birch--Swinnerton--Dyer.
-/

namespace Millennium
namespace Round218BSD

/-- A nonzero vector in a vector space determines its scalar coefficient
uniquely. -/
theorem scalar_unique_on_nonzero_vector
    {𝕜 V : Type*}
    [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (v : V) (hv : v ≠ 0)
    (a b : 𝕜)
    (h : a • v = b • v) :
    a = b := by
  have hzero : (a - b) • v = 0 := by
    rw [sub_smul, h]
    simp
  rcases smul_eq_zero.mp hzero with hab | hvzero
  · exact sub_eq_zero.mp hab
  · exact False.elim (hv hvzero)

/-- Mutual divisibility closes the positive numerator/denominator magnitude
comparison after all prime exponents have been matched. -/
theorem mutual_divisibility_closes_magnitude
    (m n : ℕ)
    (hmn : m ∣ n)
    (hnm : n ∣ m) :
    m = n := by
  exact Nat.dvd_antisymm hmn hnm

/-- Positivity eliminates the remaining sign from a `±1` ambiguity. -/
theorem positivity_kills_sign_ambiguity
    (q : ℤ)
    (hunit : q = 1 ∨ q = -1)
    (hpos : 0 < q) :
    q = 1 := by
  rcases hunit with hq | hq
  · exact hq
  · omega

/-- Checking only the primes two and three does not determine a rational
integer unit: one and five are distinct, and both are coprime to six. -/
theorem finite_local_unit_ambiguity :
    (1 : ℕ) ≠ 5 ∧ Nat.Coprime 6 1 ∧ Nat.Coprime 6 5 := by
  norm_num

/-- Once a comparison scalar is proved to be one, the two line elements are
identical. -/
theorem scalar_one_closes_line_comparison
    {𝕜 V : Type*}
    [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (zAnalytic zAlgebraic : V)
    (q : 𝕜)
    (hcompare : zAnalytic = q • zAlgebraic)
    (hq : q = 1) :
    zAnalytic = zAlgebraic := by
  simpa [hq] using hcompare

/-- Equality in one faithful realization of a rational line already determines
the rational scalar; this records the typed direction only. -/
theorem injective_realization_reflects_line_equality
    {V W : Type*}
    (realize : V → W)
    (hinj : Function.Injective realize)
    (x y : V)
    (hxy : realize x = realize y) :
    x = y := by
  exact hinj hxy

#print axioms scalar_unique_on_nonzero_vector
#print axioms mutual_divisibility_closes_magnitude
#print axioms positivity_kills_sign_ambiguity
#print axioms finite_local_unit_ambiguity
#print axioms scalar_one_closes_line_comparison
#print axioms injective_realization_reflects_line_equality

end Round218BSD
end Millennium
