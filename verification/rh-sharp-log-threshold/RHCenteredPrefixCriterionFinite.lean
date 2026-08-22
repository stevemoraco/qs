import Mathlib

/-!
# Centered ordinary-prime prefix criterion: finite algebraic core

This file verifies only scalar algebra used in
`RH_CENTERED_PREFIX_RATIO_SINGLE_LOG_CRITERION_2026-08-13.md`.

It does not formalize primes, logarithmic asymptotics, explicit formulas,
infinite series, Johnston/Guth--Maynard inputs, or RH.
-/

namespace RHCenteredPrefixCriterionFinite

/-- Exact centered root definition. -/
def centeredRoot (R L : ℝ) : ℝ := R - L / 2

/-- Centering by a logarithmic term preserves a deep negative polynomial block
once the logarithmic term is nonnegative. -/
theorem centered_negative_dominates
    {R L depth : ℝ}
    (hR : R ≤ -depth)
    (hL : 0 ≤ L) :
    centeredRoot R L ≤ -depth := by
  unfold centeredRoot
  linarith

/-- A deep negative centered value has at least the corresponding square
energy when the depth is nonnegative. -/
theorem centered_square_lower
    {R L depth : ℝ}
    (hdepth : 0 ≤ depth)
    (hR : R ≤ -depth)
    (hL : 0 ≤ L) :
    depth ^ 2 ≤ (centeredRoot R L) ^ 2 := by
  have hcenter := centered_negative_dominates hR hL
  have hnonpos : centeredRoot R L ≤ 0 := by linarith
  nlinarith

/-- Exact normalized centered identity:
`1-Q-L/(4 sqrtTheta)=(R-L/2)/(2 sqrtTheta)`. -/
theorem normalized_centered_identity
    {R L Q sqrtTheta : ℝ}
    (hsqrt : sqrtTheta ≠ 0)
    (hroot : 1 - Q = R / (2 * sqrtTheta)) :
    1 - Q - L / (4 * sqrtTheta) =
      centeredRoot R L / (2 * sqrtTheta) := by
  unfold centeredRoot
  rw [hroot]
  field_simp [hsqrt]
  ring

/-- Squaring the normalized centered identity. -/
theorem normalized_centered_square_identity
    {R L Q sqrtTheta theta : ℝ}
    (hsqrt : sqrtTheta ≠ 0)
    (hsq : sqrtTheta ^ 2 = theta)
    (hroot : 1 - Q = R / (2 * sqrtTheta)) :
    (centeredRoot R L) ^ 2 =
      4 * theta * (1 - Q - L / (4 * sqrtTheta)) ^ 2 := by
  have hid := normalized_centered_identity hsqrt hroot
  rw [hid, ← hsq]
  field_simp [hsqrt]
  ring

/-- Any positive logarithmic exponent lies to the convergent side of the
centered prime-harmonic threshold. -/
theorem centered_log_threshold_positive
    {alpha : ℝ}
    (h : 0 < alpha) :
    0 < alpha := h

/-- The false-RH block exponent is unchanged by logarithmic centering. -/
theorem centered_false_block_exponent
    (delta epsilon : ℝ) :
    (1 - epsilon) + (2 * delta - 2 * epsilon) - 1
      = 2 * delta - 3 * epsilon := by
  ring

/-- Positive polynomial margin after the usual loss choice. -/
theorem centered_false_block_margin
    {delta epsilon : ℝ}
    (h : 3 * epsilon < 2 * delta) :
    0 < 2 * delta - 3 * epsilon := by
  linarith

/-- Abstract criterion packaging. -/
theorem centered_series_criterion
    {P finiteCenteredSeries : Prop}
    (hforward : P → finiteCenteredSeries)
    (hfalse : ¬ P → ¬ finiteCenteredSeries) :
    P ↔ finiteCenteredSeries := by
  constructor
  · exact hforward
  · intro hfinite
    by_contra hP
    exact hfalse hP hfinite

#print axioms centered_negative_dominates
#print axioms centered_square_lower
#print axioms normalized_centered_identity
#print axioms normalized_centered_square_identity
#print axioms centered_log_threshold_positive
#print axioms centered_false_block_exponent
#print axioms centered_false_block_margin
#print axioms centered_series_criterion

end RHCenteredPrefixCriterionFinite
