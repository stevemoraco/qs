import Mathlib

open scoped BigOperators

namespace Millennium.YangMills

/-!
# Finite template register envelope

Finite bookkeeping only. If a source construction has finitely many template
species with nonnegative support-radius bounds, the sum of those radii is one
uniform radius bound for every species. Combined with a live-pivot spacing
strictly larger than that envelope, no bounded template incidence can contain
two separated pivots.

This file does not prove that Kirk v4's `Q_tail,fin` is exhausted by such a
finite register. That source-classification theorem is the live hypothesis.
It does not prove HT5/6.30, a Yang--Mills gap, OS reconstruction, or Clay.
-/

/-- Every nonnegative member of a finite real-valued family is bounded by the
sum of the family. -/
theorem finite_template_radius_le_sum
    {ι : Type*} [Fintype ι]
    (D : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i)
    (i : ι) :
    D i ≤ ∑ j, D j := by
  exact Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)

/-- A finite register of nonnegative template radii admits the explicit uniform
envelope `∑ j, D j`. -/
theorem finite_template_uniform_radius
    {ι : Type*} [Fintype ι]
    (D : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i) :
    ∀ i, D i ≤ ∑ j, D j := by
  intro i
  exact finite_template_radius_le_sum D hD i

/-- Source-facing multipivot exclusion for a finite template register: if the
pivot spacing exceeds the finite-register radius envelope, no pair distance can
be both at least the pivot spacing and bounded by the radius of any template
species. -/
theorem finite_template_register_excludes_two_pivots
    {ι : Type*} [Fintype ι]
    (D : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i)
    {R pairDist : ℝ}
    (hR : (∑ j, D j) < R)
    (i : ι)
    (hpivotSep : R ≤ pairDist)
    (hpairInTemplate : pairDist ≤ D i) : False := by
  have hi : D i ≤ ∑ j, D j := finite_template_radius_le_sum D hD i
  linarith

#print axioms finite_template_radius_le_sum
#print axioms finite_template_uniform_radius
#print axioms finite_template_register_excludes_two_pivots

end Millennium.YangMills
