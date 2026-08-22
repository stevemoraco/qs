import Mathlib

/-!
# RH B154 prime-harmonic square finite core

This file formalizes only deterministic algebra used by the human B154 reduction:

* exact cancellation of a reciprocal-prime jump against the prime-count jump;
* finite prefix reweighting `x * sum w - card = sum (x*w-1)`;
* square-cell width arithmetic;
* a finite excursion-transport inequality;
* zero negative-count iff all sampled values are nonnegative.

It does **not** formalize Bhattacharya--Martin--Simpson Theorem 1.6, Mertens'
theorem, prime counting, logarithmic integrals, zeta, BGST/Hermite spectral theory,
or the Riemann hypothesis.
-/

open Finset
open scoped BigOperators

namespace RHPrimeHarmonicSquareFinite

/-- At an event located at `p`, a jump `1/p` in the reciprocal-prime state
is cancelled exactly by a unit jump in the prime-count state after multiplying
by the physical coordinate `p`. -/
theorem reciprocal_prime_event_jump_cancels
    {p r c : ℝ} (hp : p ≠ 0) :
    p * (r + p⁻¹) - (c + 1) = p * r - c := by
  field_simp [hp]
  ring

/-- Finite prefix reweighting used to turn
`x * sum_{p<=x} 1/p - pi(x)` into a sum of nonnegative event terms. -/
theorem prefix_reweight_identity
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (x : ℝ) :
    (∑ i in s, (x * w i - 1)) =
      x * (∑ i in s, w i) - (s.card : ℝ) := by
  rw [Finset.sum_sub_distrib]
  simp [Finset.mul_sum]

/-- A point lying between consecutive real squares is at physical distance less
than `2n+1` from the left square. -/
theorem square_cell_width
    {n x : ℝ}
    (hn : 0 ≤ n)
    (hlo : n ^ 2 ≤ x)
    (hi : x < (n + 1) ^ 2) :
    0 ≤ x - n ^ 2 ∧ x - n ^ 2 < 2 * n + 1 := by
  constructor <;> nlinarith

/-- A negative excursion deeper than the interpolation error remains negative
at the sampled point. -/
theorem negative_excursion_survives_sampling
    {fx fsamp amp C L : ℝ}
    (hamp : 0 < amp)
    (hdepth : fx ≤ -L * amp)
    (herr : |fsamp - fx| ≤ C * amp)
    (hCL : C < L) :
    fsamp < 0 := by
  have hupper : fsamp - fx ≤ C * amp := (abs_le.mp herr).2
  nlinarith

/-- Number of negative entries in a finite sample. -/
def negativeCount
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) : ℕ :=
  (s.filter fun i => f i < 0).card

/-- Zero negative count is exactly coordinatewise nonnegativity. -/
theorem negativeCount_eq_zero_iff
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    negativeCount s f = 0 ↔ ∀ i ∈ s, 0 ≤ f i := by
  classical
  simp [negativeCount, not_lt]

#print axioms reciprocal_prime_event_jump_cancels
#print axioms prefix_reweight_identity
#print axioms square_cell_width
#print axioms negative_excursion_survives_sampling
#print axioms negativeCount_eq_zero_iff

end RHPrimeHarmonicSquareFinite
