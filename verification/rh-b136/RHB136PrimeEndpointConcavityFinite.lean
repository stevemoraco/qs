import Mathlib

/-!
# RH B136 prime-endpoint finite core

Finite algebra only.

This file formalizes three load-bearing deterministic shadows of the B136
ordinary-prime endpoint reduction:

* a chord lower bound plus nonnegative endpoint values forces a nonnegative
  interior value;
* the finite prefix reweighting identity used to rewrite
  `X * sum(log p / p) - theta(X)` as one weighted prime-prefix sum;
* zero negative-entry count is exactly coordinatewise nonnegativity.

It does **not** formalize Zhao's analytic theorem, prime numbers, Mertens'
theorem, concavity of the actual mean-Mertens function, zeta, BGST matrices,
or the Riemann hypothesis.
-/

namespace RHB136PrimeEndpointConcavityFinite

open Finset

/-- If a function value lies above the chord joining two nonnegative endpoint
values, then that interior value is nonnegative. This is the finite scalar core
used after proving concavity on one consecutive-prime gap. -/
theorem chord_nonnegative_of_endpoint_nonnegative
    (a b x fa fb fx : ℝ)
    (hab : a < b)
    (hax : a ≤ x)
    (hxb : x ≤ b)
    (hfa : 0 ≤ fa)
    (hfb : 0 ≤ fb)
    (hchord :
      (b - x) * fa + (x - a) * fb ≤ (b - a) * fx) :
    0 ≤ fx := by
  have hbx : 0 ≤ b - x := sub_nonneg.mpr hxb
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hax
  have hrhs : 0 ≤ (b - x) * fa + (x - a) * fb := by
    exact add_nonneg (mul_nonneg hbx hfa) (mul_nonneg hxa hfb)
  have hprod : 0 ≤ (b - a) * fx := hrhs.trans hchord
  have hba : 0 < b - a := sub_pos.mpr hab
  nlinarith

/-- Exact finite reweighting identity behind the B136 prime-endpoint formula.
No primality hypothesis is present: `t i` can be any nonzero event location. -/
theorem finite_prefix_reweight_identity
    {ι : Type*} (s : Finset ι)
    (X : ℝ) (t ell : ι → ℝ) :
    X * (∑ i ∈ s, ell i / t i) - (∑ i ∈ s, ell i) =
      ∑ i ∈ s, (X / t i - 1) * ell i := by
  rw [Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Finite diagonal-inertia shadow: having no negative coordinate is exactly
coordinatewise nonnegativity. `negativeCount` is the diagonal matrix negative
index before introducing any spectral-library machinery. -/
def negativeCount {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℕ :=
  (Finset.univ.filter fun i => a i < 0).card

/-- Zero finite negative count iff every coordinate is nonnegative. -/
theorem negativeCount_eq_zero_iff
    {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    negativeCount a = 0 ↔ ∀ i, 0 ≤ a i := by
  classical
  simp [negativeCount, not_lt]

#print axioms chord_nonnegative_of_endpoint_nonnegative
#print axioms finite_prefix_reweight_identity
#print axioms negativeCount_eq_zero_iff

end RHB136PrimeEndpointConcavityFinite
