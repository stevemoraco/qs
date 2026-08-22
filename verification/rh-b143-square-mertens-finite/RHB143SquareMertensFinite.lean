import Mathlib

/-!
# RH B143 square-Mertens finite core

Finite real/natural-number algebra only.

This file formalizes the load-bearing deterministic inequalities used by the
human B143 reduction:

* an ordinary-prime state that differs from a von-Mangoldt state by a positive
  proper-power tail lies above the von-Mangoldt state;
* a quantitative upper bound on that tail transfers a one-sided lower bound;
* one-sided interpolation through a downward drift budget preserves a lower
  floor with exactly the added drift debt;
* the physical width of the square cell `n^2 -> (n+1)^2` is at most `3 n` for
  `n >= 1`;
* shifting by an allowed lower-floor budget converts the scalar criterion to a
  zero-threshold nonnegativity statement.

It does **not** formalize primes, Mertens' theorem, Mellin transforms, Landau's
theorem, zeta, matrix spectral theory, or RH.
-/

namespace RHB143SquareMertensFinite

/-- If the prime-only state is the von-Mangoldt state plus a nonnegative tail,
then it lies above the von-Mangoldt state. -/
theorem positive_tail_order
    (mPrime mLambda tail : ℝ)
    (hrel : mPrime = mLambda + tail)
    (htail : 0 ≤ tail) :
    mLambda ≤ mPrime := by
  linarith

/-- If the proper-power tail is at most `err`, a lower bound for the prime-only
state transfers to the von-Mangoldt state with only the added `err` debt. -/
theorem positive_tail_lower_transfer
    (mPrime mLambda tail floor err : ℝ)
    (hrel : mPrime = mLambda + tail)
    (htail : tail ≤ err)
    (hlower : -floor ≤ mPrime) :
    -(floor + err) ≤ mLambda := by
  linarith

/-- One-sided interpolation through a downward drift budget.  Upward jumps only
improve the conclusion, so the finite shadow is simply `sample-drift <= value`. -/
theorem one_sided_drift_transfer
    (sample value floor drift : ℝ)
    (hsample : -floor ≤ sample)
    (hvalue : sample - drift ≤ value) :
    -(floor + drift) ≤ value := by
  linarith

/-- The square-cell physical width is `2 n + 1`, hence at most `3 n` once
`n >= 1`. -/
theorem square_cell_width_bound
    (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ 2 - (n : ℝ) ^ 2 ≤ 3 * (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  nlinarith

/-- A scalar lower-floor condition is exactly a zero-threshold nonnegativity
condition after adding the allowed floor. -/
theorem lower_floor_iff_shifted_nonnegative
    (value floor : ℝ) :
    -floor ≤ value ↔ 0 ≤ value + floor := by
  constructor <;> intro h <;> linarith

#print axioms positive_tail_order
#print axioms positive_tail_lower_transfer
#print axioms one_sided_drift_transfer
#print axioms square_cell_width_bound
#print axioms lower_floor_iff_shifted_nonnegative

end RHB143SquareMertensFinite
