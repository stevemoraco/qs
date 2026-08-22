import Mathlib

/-!
# RH B136/B136A prime-endpoint finite core

Finite algebra only.

This file formalizes deterministic shadows of the B136 ordinary-prime endpoint
reduction and the B136A square-checkpoint sparsification:

* a chord lower bound plus nonnegative endpoint values forces a nonnegative
  interior value;
* the finite prefix reweighting identity used to rewrite
  `X * sum(log p / p) - theta(X)` as one weighted prime-prefix sum;
* zero negative-entry count is exactly coordinatewise nonnegativity;
* one square cell has physical width at most `2 n + 1`;
* a negative excursion survives transport when the transport error is smaller
  than its depth.

It does **not** formalize Zhao's analytic theorem, prime numbers, Mertens'
theorem, concavity or Lipschitz control of the actual mean-Mertens function,
zeta, BGST matrices, or the Riemann hypothesis.
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
No primality hypothesis is present: `t i` can be any event location. -/
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

/-- B136A square-cell geometry: if `x` lies between `n²` and `(n+1)²`, then
its distance from the lower square is at most `2n+1`. -/
theorem square_cell_distance_bound
    (n x : ℝ) (hn : 0 ≤ n)
    (hlo : n ^ 2 ≤ x) (hhi : x ≤ (n + 1) ^ 2) :
    0 ≤ x - n ^ 2 ∧ x - n ^ 2 ≤ 2 * n + 1 := by
  constructor
  · linarith
  · nlinarith

/-- If a value is negative by depth `depth`, and transport changes it by at most
`err < depth`, the transported value is still negative. This is the finite
firewall used when moving an off-grid negative excursion to the nearest square
checkpoint. -/
theorem negative_survives_bounded_transport
    (atX atY depth err : ℝ)
    (hX : atX ≤ -depth)
    (hmove : |atY - atX| ≤ err)
    (hstrict : err < depth) :
    atY < 0 := by
  have hupper : atY - atX ≤ err := (abs_le.mp hmove).2
  linarith

#print axioms chord_nonnegative_of_endpoint_nonnegative
#print axioms finite_prefix_reweight_identity
#print axioms negativeCount_eq_zero_iff
#print axioms square_cell_distance_bound
#print axioms negative_survives_bounded_transport

end RHB136PrimeEndpointConcavityFinite
