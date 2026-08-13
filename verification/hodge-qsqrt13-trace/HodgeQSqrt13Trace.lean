import Mathlib

/-!
# Finite trace-discriminant certificate for the Q(sqrt 13) Hodge lane

This file formalizes only the exact rational arithmetic behind a proposed
non-scalarity test. It does not formalize K3 surfaces, Hodge structures,
algebraic cycles, the Lefschetz trace formula, or the Hodge conjecture.
-/

namespace HodgeQSqrt13Trace

/-- If the two real embeddings of `a + b*sqrt(13)` each occur ten times,
the rank-20 trace discriminant is exactly `5200*b^2`. -/
theorem trace_discriminant (a b : ℚ) :
    20 * (20 * (a ^ 2 + 13 * b ^ 2)) - (20 * a) ^ 2 = 5200 * b ^ 2 := by
  ring

/-- The exact trace discriminant is nonzero exactly when the
`sqrt(13)` coefficient is nonzero. -/
theorem trace_discriminant_ne_zero_iff (a b : ℚ) :
    20 * (20 * (a ^ 2 + 13 * b ^ 2)) - (20 * a) ^ 2 ≠ 0 ↔ b ≠ 0 := by
  rw [trace_discriminant]
  constructor
  · intro h hb
    subst b
    simp at h
  · intro hb
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)

#print axioms trace_discriminant
#print axioms trace_discriminant_ne_zero_iff

end HodgeQSqrt13Trace
