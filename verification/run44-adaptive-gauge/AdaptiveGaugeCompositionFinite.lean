import Mathlib

/-!
# Run44 adaptive-gauge composition finite core

HONESTY BOUNDARY

This file formalizes only finite scalar algebra used by the Run44
cross-problem accounting firewall:

* exact slope-cancelled Bregman bookkeeping once affine/tangent expansions are
  already supplied as hypotheses;
* strict loss when the coefficient and Bregman defect are positive;
* the exact debt incurred by replacing two local weights by one fixed global
  weight;
* a two-step positive-weight counterexample where both adaptively weighted
  local terms vanish while every fixed global weight leaves residual one.

It does not formalize logarithmic integrals, concavity, primes, zeta, RH,
Navier--Stokes, circuits, BSD fundamental lines, Hodge cycles, Yang--Mills,
or any official Clay statement.
-/

namespace MillenniumBraid
namespace Run44AdaptiveGauge

/-- If an affine coordinate and a tangent-minus-defect coordinate have their
linear slopes exactly cancelled, the combined value equals its reference value
minus the weighted defect. -/
theorem slope_cancelled_bregman_identity
    (H H₀ A A₀ L s e e₀ λ B : ℝ)
    (hH : H = H₀ + L * (e - e₀))
    (hA : A = A₀ + s * (e - e₀) - B)
    (hcancel : L + λ * s = 0) :
    H + λ * A = H₀ + λ * A₀ - λ * B := by
  rw [hH, hA]
  calc
    H₀ + L * (e - e₀) + λ * (A₀ + s * (e - e₀) - B)
        = H₀ + λ * A₀ + (L + λ * s) * (e - e₀) - λ * B := by
            ring
    _ = H₀ + λ * A₀ - λ * B := by
          rw [hcancel]
          ring

/-- Positive coefficient and positive Bregman defect turn slope cancellation
into a strict drop from the reference value. -/
theorem slope_cancelled_positive_defect_strict_drop
    (H H₀ A A₀ L s e e₀ λ B : ℝ)
    (hH : H = H₀ + L * (e - e₀))
    (hA : A = A₀ + s * (e - e₀) - B)
    (hcancel : L + λ * s = 0)
    (hλ : 0 < λ)
    (hB : 0 < B) :
    H + λ * A < H₀ + λ * A₀ := by
  have hid := slope_cancelled_bregman_identity
    H H₀ A A₀ L s e e₀ λ B hH hA hcancel
  rw [hid]
  nlinarith

/-- Two locally selected weights equal one fixed globally selected weight plus
an exact adaptive-gauge debt. -/
theorem two_step_adaptive_weight_debt
    (h₁ h₂ a₁ a₂ λ₁ λ₂ λ : ℝ) :
    (h₁ + λ₁ * a₁) + (h₂ + λ₂ * a₂)
      = (h₁ + h₂) + λ * (a₁ + a₂)
        + (λ₁ - λ) * a₁ + (λ₂ - λ) * a₂ := by
  ring

/-- Both local terms in the minimal positive-weight counterexample vanish. -/
theorem positive_adaptive_weights_cancel_each_local_term :
    ((-1 : ℝ) + 1 * 1 = 0) ∧
    ((2 : ℝ) + 2 * (-1) = 0) := by
  norm_num

/-- The same two local data leave residual one for every single fixed global
weight. -/
theorem every_fixed_global_weight_leaves_residual_one (λ : ℝ) :
    ((-1 : ℝ) + λ * 1) + (2 + λ * (-1)) = 1 := by
  ring

/-- In the minimal counterexample the exact adaptive-gauge debt is `-1`. -/
theorem minimal_counterexample_gauge_debt (λ : ℝ) :
    ((1 : ℝ) - λ) * 1 + (2 - λ) * (-1) = -1 := by
  ring

#print axioms slope_cancelled_bregman_identity
#print axioms slope_cancelled_positive_defect_strict_drop
#print axioms two_step_adaptive_weight_debt
#print axioms positive_adaptive_weights_cancel_each_local_term
#print axioms every_fixed_global_weight_leaves_residual_one
#print axioms minimal_counterexample_gauge_debt

end Run44AdaptiveGauge
end MillenniumBraid
