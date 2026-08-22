import Mathlib

/-!
# B211 finite A1 -> B46 transform core

Finite algebra only.

This file formalizes two load-bearing scalar facts from the B211 human proof:

1. after the Zhao denominator has been differentiated once, the remaining
   half-shift denominator cancels exactly against the Haar integral correction;
2. a nonnegative scalar weight times a phase bounded by one in absolute value
   cannot exceed that weight in absolute value.

The source does **not** formalize Zhao's theorem, primes, the B129 convolution
identity, Xi, Deng--Yang--Lu, matrix functional calculus, zeta zeros, B46, RH,
or not-RH.
-/

namespace RHB211A1B46TransformFinite

/-- Denominator-cleared algebra behind
`T_h[e^{-t/2} d/dt Z_s] = -m_h(s)/s * e^{st}`.

The analytic proof supplies `m = m_h(s)`; this theorem checks only the exact
rational cancellation. -/
theorem mode_cancellation_cleared (s m : ℂ) (hs : s ≠ 0) :
    ((1 / 2 : ℂ) - s) * (-m / s) = m - m / (2 * s) := by
  field_simp [hs]
  ring

/-- Scalar atom behind the finite real-support contraction: a nonnegative
weight times any real phase in the unit interval has absolute contribution at
most the weight. -/
theorem nonnegative_weight_phase_bound
    (a z : ℝ) (ha : 0 ≤ a) (hz : |z| ≤ 1) :
    |a * z| ≤ a := by
  rw [abs_mul, abs_of_nonneg ha]
  have h := mul_le_mul_of_nonneg_left hz ha
  simpa using h

/-- The same scalar bound in the cosine-shaped form used by the finite B46
real-node contribution. -/
theorem nonnegative_weight_cosine_bound
    (a theta : ℝ) (ha : 0 ≤ a) :
    |a * Real.cos theta| ≤ a := by
  apply nonnegative_weight_phase_bound a (Real.cos theta) ha
  exact abs_cos_le_one theta

#print axioms mode_cancellation_cleared
#print axioms nonnegative_weight_phase_bound
#print axioms nonnegative_weight_cosine_bound

end RHB211A1B46TransformFinite
