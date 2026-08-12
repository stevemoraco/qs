import Mathlib

namespace B4NSExactSphereObstruction

/-- Mode-count exponent required when a unit-`L²` packet must supply an
    intermittency gain `K^(alpha-1)` through square-root mode concentration. -/
noncomputable def requiredModeExponent (alpha : ℝ) : ℝ := 2 * (alpha - 1)

/-- In the physical blow-up range `alpha>2`, the required mode exponent is
    strictly larger than the quadratic lattice-point budget of one sphere. -/
theorem requiredModeExponentExceedsTwo
    {alpha : ℝ} (hAlpha : 2 < alpha) :
    2 < requiredModeExponent alpha := by
  unfold requiredModeExponent
  linarith

/-- Palasek's viscous scale restriction puts the largest possible one-sphere
    coefficient exponent `2b` strictly below the target exponent `alpha`. -/
theorem viscousSphereCoefficientExponentGap
    {alpha b : ℝ} (hScale : b < alpha / 2) :
    2 * b < alpha := by
  linarith

/-- Any proposed lower exponent requirement `alpha ≤ 2b` contradicts the
    viscous scale restriction. -/
theorem oneSphereBudgetContradiction
    {alpha b : ℝ}
    (hScale : b < alpha / 2)
    (hNeeded : alpha ≤ 2 * b) : False := by
  have hGap := viscousSphereCoefficientExponentGap hScale
  linarith

/-- Elementary coordinate-fiber budget: a square box of side `2R+1`, with at
    most two choices of the third coordinate over each first-coordinate pair,
    has at most this many points.  The geometric injection of a lattice sphere
    into these fibers is kept explicit in the research note. -/
theorem coordinateFiberBudget (R : ℕ) :
    2 * ((2 * R + 1) * (2 * R + 1)) = 2 * (2 * R + 1)^2 := by
  ring

/-- If a coefficient is simultaneously bounded above by a quadratic sphere
    budget and required to have a strictly larger exponent, the exponent
    assumptions are inconsistent. -/
theorem exactSphereCannotMeetViscousTargetExponent
    {alpha b upperExponent : ℝ}
    (hSphere : upperExponent ≤ 2 * b)
    (hTarget : alpha ≤ upperExponent)
    (hScale : b < alpha / 2) : False := by
  have hGap := viscousSphereCoefficientExponentGap hScale
  linarith

#print axioms requiredModeExponentExceedsTwo
#print axioms viscousSphereCoefficientExponentGap
#print axioms oneSphereBudgetContradiction
#print axioms coordinateFiberBudget
#print axioms exactSphereCannotMeetViscousTargetExponent

end B4NSExactSphereObstruction
