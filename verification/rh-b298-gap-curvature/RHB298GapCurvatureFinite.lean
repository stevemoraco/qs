import Mathlib

/-!
# RH B298 finite prime-gap curvature core

This file formalizes only the elementary real inequalities used in RH #1575 / B298:
for `δ ≥ 0`,

`0 ≤ δ - log(1+δ) ≤ δ²/2`,

and its nonnegative weighted form. It does not formalize primes, Chebyshev theta,
Stadlmann's mean-square prime-gap theorem, dyadic asymptotics, zeta, RH, or not-RH.
-/

namespace RHB298GapCurvature

/-- The logarithmic gap-curvature loss is nonnegative and bounded by half the
square of the relative gap. This estimate is global for every `δ ≥ 0`; no
small-gap Taylor assumption is used. -/
theorem log_curvature_bounds (δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ δ - Real.log (1 + δ) ∧
      δ - Real.log (1 + δ) ≤ δ ^ 2 / 2 := by
  constructor
  · have hpos : 0 < 1 + δ := by linarith
    have hlog := Real.log_le_sub_one_of_pos hpos
    linarith
  · have hlog := Real.le_log_one_add_of_nonneg hδ
    have hden : 0 < δ + 2 := by linarith
    have hcub : 0 ≤ δ * δ ^ 2 := mul_nonneg hδ (sq_nonneg δ)
    have hrat : δ - δ ^ 2 / 2 ≤ 2 * δ / (δ + 2) := by
      rw [le_div_iff₀ hden]
      nlinarith
    linarith

/-- Multiplying the gap-curvature loss by a nonnegative event weight preserves
the quadratic ceiling. -/
theorem weighted_log_curvature_bounds
    (p δ : ℝ) (hp : 0 ≤ p) (hδ : 0 ≤ δ) :
    0 ≤ p * (δ - Real.log (1 + δ)) ∧
      p * (δ - Real.log (1 + δ)) ≤ p * (δ ^ 2 / 2) := by
  obtain ⟨hlo, hhi⟩ := log_curvature_bounds δ hδ
  constructor
  · exact mul_nonneg hp hlo
  · exact mul_le_mul_of_nonneg_left hhi hp

#print axioms log_curvature_bounds
#print axioms weighted_log_curvature_bounds

end RHB298GapCurvature
