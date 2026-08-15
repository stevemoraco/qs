import Mathlib

/-!
# RH B113 finite Fermi log-determinant core

Finite real/order algebra only.

The human B113 reduction replaces one-sided positive variation on a finite block
by a single finite-temperature determinant.  The load-bearing scalar fact is

  exp (tau * x_+) <= 1 + exp (tau*x) <= 2 * exp (tau * x_+),

for `tau >= 0`, where `x_+ = max x 0`.  Multiplying these inequalities over a
finite family yields the exact product sandwich used before taking logarithms.

This file deliberately does not formalize matrix exponentials/determinants,
primes, B109B, zeta, or RH.
-/

open scoped BigOperators

namespace RHB113FermiLogdetFinite

/-- One scalar Fermi factor differs from the positive-part exponential by at
most a factor two. -/
theorem exp_pospart_factor_bounds
    (tau x : ℝ) (htau : 0 ≤ tau) :
    Real.exp (tau * max x 0) ≤ 1 + Real.exp (tau * x) ∧
    1 + Real.exp (tau * x) ≤ 2 * Real.exp (tau * max x 0) := by
  by_cases hx : x ≤ 0
  · have hmax : max x 0 = 0 := max_eq_right hx
    have htx : tau * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htau hx
    have hexp_le : Real.exp (tau * x) ≤ 1 := by
      have h := Real.exp_le_exp.mpr htx
      simpa using h
    rw [hmax]
    constructor
    · have hpos : 0 < Real.exp (tau * x) := Real.exp_pos _
      simp
      linarith
    · simp
      linarith
  · have hx0 : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
    have hmax : max x 0 = x := max_eq_left hx0
    have htx : 0 ≤ tau * x := mul_nonneg htau hx0
    have hone_le : 1 ≤ Real.exp (tau * x) := by
      have h := Real.exp_le_exp.mpr htx
      simpa using h
    rw [hmax]
    constructor
    · linarith [Real.exp_pos (tau * x)]
    · linarith

/-- Finite product lower bound. -/
theorem finite_fermi_product_lower
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (tau : ℝ) (x : ι → ℝ) (htau : 0 ≤ tau) :
    (∏ i in s, Real.exp (tau * max (x i) 0)) ≤
      ∏ i in s, (1 + Real.exp (tau * x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfactor := (exp_pospart_factor_bounds tau (x a) htau).1
      have hleft : 0 ≤ ∏ i in s, Real.exp (tau * max (x i) 0) := by positivity
      have hright : 0 ≤ 1 + Real.exp (tau * x a) := by positivity
      exact mul_le_mul hfactor ih hleft hright

/-- Finite product upper bound. -/
theorem finite_fermi_product_upper
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (tau : ℝ) (x : ι → ℝ) (htau : 0 ≤ tau) :
    (∏ i in s, (1 + Real.exp (tau * x i))) ≤
      ∏ i in s, (2 * Real.exp (tau * max (x i) 0)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfactor := (exp_pospart_factor_bounds tau (x a) htau).2
      have hleft : 0 ≤ ∏ i in s, (1 + Real.exp (tau * x i)) := by positivity
      have hright : 0 ≤ 2 * Real.exp (tau * max (x a) 0) := by positivity
      exact mul_le_mul hfactor ih hleft hright

/-- Combined finite product sandwich, the exact finite algebra used by B113
before applying logarithms and the matrix spectral theorem. -/
theorem finite_fermi_product_sandwich
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (tau : ℝ) (x : ι → ℝ) (htau : 0 ≤ tau) :
    (∏ i in s, Real.exp (tau * max (x i) 0)) ≤
      ∏ i in s, (1 + Real.exp (tau * x i)) ∧
    (∏ i in s, (1 + Real.exp (tau * x i))) ≤
      ∏ i in s, (2 * Real.exp (tau * max (x i) 0)) := by
  exact ⟨finite_fermi_product_lower s tau x htau,
    finite_fermi_product_upper s tau x htau⟩

/-- Hostile fixed-temperature witness at the scalar level: a tiny negative depth
has zero positive part while its Fermi factor stays strictly above one. -/
theorem tiny_negative_has_zero_positive_part_but_positive_fermi_excess
    (L tau : ℝ) (hL : 0 < L) :
    max (-1 / L) 0 = 0 ∧
      1 < 1 + Real.exp (tau * (-1 / L)) := by
  constructor
  · apply max_eq_right
    have hdiv : 0 < 1 / L := one_div_pos.mpr hL
    linarith
  · have hpos := Real.exp_pos (tau * (-1 / L))
    linarith

#print axioms exp_pospart_factor_bounds
#print axioms finite_fermi_product_lower
#print axioms finite_fermi_product_upper
#print axioms finite_fermi_product_sandwich
#print axioms tiny_negative_has_zero_positive_part_but_positive_fermi_excess

end RHB113FermiLogdetFinite
