import Mathlib

/-!
# RH B160 negative-run/path-inertia finite core

Finite order/combinatorial/real algebra only.

This source formalizes the deterministic shell of the B160 reduction:

* an all-negative run remains all-negative after shortening;
* the exact sampler-gap/run-length zero-strip exponent identity;
* a strict off-strip zero leaves a strictly larger sampled-run exponent after an
  epsilon loss;
* the hostile interval/sampler exponent subtraction is exact;
* an all-one sign word has nonzero path product, the scalar shadow of the
  `P U P` path-power detector;
* a nonzero off-diagonal path amplitude gives a two-dimensional Hermitian
  dilation with negative determinant.

It does **not** formalize Bhattacharya--Martin--Simpson, Landau's theorem,
reciprocal-prime Mertens estimates, primes, zeta zeros, matrix spectral theory,
Deng--Yang--Lü contour Hankel theory, the B46 explicit formula, or RH.
-/

namespace RHNegativeRunPathInertiaFinite

open Finset

/-- A consecutive run of negative values beginning at `start`. -/
def BadRun (x : ℕ → ℝ) (start len : ℕ) : Prop :=
  ∀ j : ℕ, j < len → x (start + j) < 0

/-- Every prefix of a negative run is again a negative run. -/
theorem badRun_prefix
    {x : ℕ → ℝ} {start small big : ℕ}
    (hsmall : small ≤ big)
    (hbig : BadRun x start big) :
    BadRun x start small := by
  intro j hj
  exact hbig j (lt_of_lt_of_le hj hsmall)

/-- Exact B160 sampler-gap/run-length strip identity. -/
theorem run_strip_exponent_identity (sigma eta : ℝ) :
    2 * ((1 / 2 : ℝ) + (sigma + eta) / 2) - 1 - sigma = eta := by
  ring

/-- A zero strictly beyond the B160 strip leaves sampled-run exponent strictly
larger than `eta` after a sufficiently small epsilon loss. -/
theorem beyond_run_strip_leaves_margin
    {beta sigma eta eps : ℝ}
    (hbeta : (1 / 2 : ℝ) + (sigma + eta) / 2 < beta)
    (heps : eps < beta - ((1 / 2 : ℝ) + (sigma + eta) / 2)) :
    eta < 2 * beta - 1 - sigma - 2 * eps := by
  linarith

/-- Hostile boundary arithmetic: an interval exponent `sigma+eta`, sampled at
spacing exponent `sigma`, leaves exactly run-count exponent `eta`. -/
theorem hostile_interval_sampler_exponent_exact (sigma eta : ℝ) :
    (sigma + eta) - sigma = eta := by
  ring

/-- Finite scalar path product attached to a consecutive sign word.  In the
matrix picture this is the coefficient appearing in a power of `P U P`. -/
def runProduct (b : ℕ → ℝ) (start len : ℕ) : ℝ :=
  ∏ j in Finset.range len, b (start + j)

/-- If every factor on the path equals one, the path product is exactly one and
hence nonzero. -/
theorem runProduct_eq_one_of_all_one
    {b : ℕ → ℝ} {start len : ℕ}
    (h : ∀ j : ℕ, j < len → b (start + j) = 1) :
    runProduct b start len = 1 := by
  unfold runProduct
  calc
    (∏ j in Finset.range len, b (start + j)) =
        ∏ j in Finset.range len, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact h j (Finset.mem_range.mp hj)
    _ = 1 := by simp

/-- A nonzero path amplitude produces the scalar determinant sign of the
`[[0,a],[a,0]]` Hermitian dilation: its determinant is strictly negative. -/
theorem nonzero_path_dilation_determinant_negative
    {a : ℝ} (ha : a ≠ 0) :
    -(a ^ 2) < 0 := by
  have hs : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  linarith

/-- At the endpoint `sigma=eta=0`, the strip center is exactly one half. -/
theorem zero_zero_run_endpoint :
    (1 / 2 : ℝ) + ((0 : ℝ) + 0) / 2 = 1 / 2 := by
  norm_num

#print axioms badRun_prefix
#print axioms run_strip_exponent_identity
#print axioms beyond_run_strip_leaves_margin
#print axioms hostile_interval_sampler_exponent_exact
#print axioms runProduct_eq_one_of_all_one
#print axioms nonzero_path_dilation_determinant_negative
#print axioms zero_zero_run_endpoint

end RHNegativeRunPathInertiaFinite
