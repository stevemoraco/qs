import Mathlib

/-!
# RH B129 Haar factor finite core

Finite real algebra only.

This file records the load-bearing scalar identities behind the B129 observation
that the B46 piecewise-linear kernel is the autocorrelation of a two-step Haar
factor and that the corresponding Mellin symbol has exactly two algebraic root
factors.

It does **not** formalize interval convolution, von Mangoldt sums, Mellin
transforms, zeta, analytic continuation, the B46 explicit formula, or RH.
-/

namespace RHB129HaarFactorFinite

/-- Inner autocorrelation algebra for `0 <= u <= h`. -/
theorem inner_overlap_identity (h c u : ℝ) :
    (h - u) * (1 + c ^ 2) - c * u =
      h * (1 + c ^ 2) - (1 + c + c ^ 2) * u := by
  ring

/-- Outer autocorrelation algebra for `h <= u <= 2h`. -/
theorem outer_overlap_identity (h c u : ℝ) :
    -c * (2 * h - u) = c * (u - 2 * h) := by
  ring

/-- Physical main-term cancellation once the adjacent-cell coefficient is `c`. -/
theorem haar_main_cancellation (c : ℝ) :
    c - (1 + c) + 1 = 0 := by
  ring

/-- Numerator of the Mellin symbol after clearing the nonzero scaling factor. -/
def symbolNumerator (c z : ℝ) : ℝ :=
  z ^ 2 - (1 + c) * z + c

/-- Exact two-root factorization of the Haar Mellin symbol. -/
theorem symbol_numerator_factorization (c z : ℝ) :
    symbolNumerator c z = (z - 1) * (z - c) := by
  dsimp [symbolNumerator]
  ring

/-- The only real algebraic roots of the cleared symbol are `1` and `c`. -/
theorem symbol_numerator_zero_iff (c z : ℝ) :
    symbolNumerator c z = 0 ↔ z = 1 ∨ z = c := by
  rw [symbol_numerator_factorization]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | hc
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- The pole-canceling root `z=c` is exact. -/
theorem symbol_vanishes_at_c (c : ℝ) :
    symbolNumerator c c = 0 := by
  rw [symbol_numerator_factorization]
  ring

/-- The second root `z=1` is exact. -/
theorem symbol_vanishes_at_one (c : ℝ) :
    symbolNumerator c 1 = 0 := by
  rw [symbol_numerator_factorization]
  ring

/-- If `c` is strictly above one, there is no cleared-symbol root strictly
between `1` and `c`.  This is the finite ordered shadow of B129 nonblindness in
the open vertical strip between the two root lines. -/
theorem symbol_nonzero_between_roots
    {c z : ℝ} (hc : 1 < c) (hz1 : 1 < z) (hzc : z < c) :
    symbolNumerator c z ≠ 0 := by
  rw [symbol_numerator_factorization]
  exact mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hz1))
    (sub_ne_zero.mpr (ne_of_lt hzc))

#print axioms inner_overlap_identity
#print axioms outer_overlap_identity
#print axioms haar_main_cancellation
#print axioms symbol_numerator_factorization
#print axioms symbol_numerator_zero_iff
#print axioms symbol_nonzero_between_roots

end RHB129HaarFactorFinite
