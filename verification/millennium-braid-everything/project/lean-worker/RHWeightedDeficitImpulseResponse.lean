import Mathlib

namespace RHWeightedDeficitImpulseResponse

/-- Algebraic core of the single-prime-power recovery budget.
If `rinv` represents `1 / sqrt n` and `ninv` represents `1 / n`, then
phase-one smooth recovery, the lower-endpoint jump, and the tail recovery
sum exactly to the initial upper-endpoint kick magnitude. -/
theorem exact_recovery_budget
    {w rinv ninv : ℝ} :
    2 * w * (rinv - ninv) + w * ninv + w * ninv = 2 * w * rinv := by
  ring

/-- The two-stage staircase contribution changes from `-2w` to `-w`
by a positive jump of exactly `w`. -/
theorem lower_endpoint_halves_staircase
    {w : ℝ} :
    (-2 * w) + w = -w := by
  ring

/-- Multiplying the smooth weighted-deficit derivative by `x` removes the
common moving denominator. This is the finite algebra behind
`x Delta' = 4x - 2 sqrt x - 2 - 2 A(x^2) + A(x)`. -/
theorem scaled_slope_algebra
    {x sx Ax Ax2 : ℝ} :
    x * (4 - 2 * sx / x - 2 / x - (2 * Ax2 - Ax) / x)
      = 4 * x - 2 * sx - 2 - 2 * Ax2 + Ax := by
  by_cases hx : x = 0
  · subst x
    simp
  · field_simp [hx]
    ring

/-- The octave bias is exactly the continuum main contribution minus the
weighted prime contribution and the constant-threshold contribution.
This theorem deliberately treats the three integrals as abstract scalars;
formal Stieltjes/integration instantiation is a separate analytic bridge. -/
theorem octave_bias_algebra
    {primeIntegral sqrtIntegral logIntegral delta : ℝ}
    (hsqrt : sqrtIntegral = delta + primeIntegral + logIntegral) :
    delta = sqrtIntegral - logIntegral - primeIntegral := by
  linarith

#print axioms exact_recovery_budget
#print axioms lower_endpoint_halves_staircase
#print axioms scaled_slope_algebra
#print axioms octave_bias_algebra

end RHWeightedDeficitImpulseResponse
