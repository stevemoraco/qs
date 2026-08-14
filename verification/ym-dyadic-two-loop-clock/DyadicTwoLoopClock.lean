import Mathlib

/-!
# Dyadic two-loop clock conversion

Finite scalar algebra for the Yang--Mills dimensional-transmutation gate.

For the standard squared-coupling beta function written in physical length time

    du/dt = 2 β₀ u² + 2 β₁ u³ + O(u⁴),

the cubic Taylor coefficient of a step of length `h` is

    b = 2 β₀ h,
    c = 2 β₁ h + 4 β₀² h².

This file formalizes the algebraic consequences of those coefficients.  In
particular, the discrete logarithmic counterterm coefficient satisfies

    h * (c / b² - 1) = β₁ / (2 β₀²),

so the universal logarithmic correction is independent of the chosen finite
step length (for Kirk's scale-two map, `h = log 2`).

This does not prove the beta-function expansion for any Yang--Mills
construction, the flow-Taylor theorem producing these coefficients, uniform
higher-order remainders, scheme matching, a physical spectral gap, or OS
reconstruction.
-/

namespace Millennium.YangMills

/-- Quadratic coefficient of a finite length-time step corresponding to the
standard squared-coupling one-loop coefficient. -/
def twoLoopStepQuadratic (beta0 h : ℝ) : ℝ := 2 * beta0 * h

/-- Cubic coefficient of a finite length-time step corresponding to the
standard squared-coupling two-loop coefficient.  The `4 beta0^2 h^2` term is
the iterated one-loop contribution. -/
def twoLoopStepCubic (beta0 beta1 h : ℝ) : ℝ :=
  2 * beta1 * h + 4 * beta0^2 * h^2

/-- The cubic step coefficient is the square of the quadratic step coefficient
plus the genuine two-loop contribution. -/
theorem twoLoopStepCubic_eq_sq_add
    (beta0 beta1 h : ℝ) :
    twoLoopStepCubic beta0 beta1 h =
      (twoLoopStepQuadratic beta0 h)^2 + 2 * beta1 * h := by
  simp [twoLoopStepQuadratic, twoLoopStepCubic]
  ring

/-- After multiplying the discrete `log u` counterterm by the physical step
length, the step size cancels exactly. -/
theorem step_logCounterterm_is_step_independent
    {beta0 beta1 h : ℝ}
    (hbeta0 : beta0 ≠ 0)
    (hh : h ≠ 0) :
    h *
        (twoLoopStepCubic beta0 beta1 h /
            (twoLoopStepQuadratic beta0 h)^2 - 1) =
      beta1 / (2 * beta0^2) := by
  simp [twoLoopStepQuadratic, twoLoopStepCubic]
  field_simp [hbeta0, hh]
  ring

/-- Equivalently, the coefficient multiplying `log (1/u)` in the crossing
clock has the opposite universal sign. -/
theorem step_crossingLogCoeff_is_step_independent
    {beta0 beta1 h : ℝ}
    (hbeta0 : beta0 ≠ 0)
    (hh : h ≠ 0) :
    h *
        (1 - twoLoopStepCubic beta0 beta1 h /
            (twoLoopStepQuadratic beta0 h)^2) =
      -(beta1 / (2 * beta0^2)) := by
  simp [twoLoopStepQuadratic, twoLoopStepCubic]
  field_simp [hbeta0, hh]
  ring

/-- Any independently established continuum value of the universal ratio is
transported exactly to the finite-step logarithmic clock coefficient. -/
theorem step_logCounterterm_transport
    {beta0 beta1 h xi : ℝ}
    (hbeta0 : beta0 ≠ 0)
    (hh : h ≠ 0)
    (hxi : beta1 / (2 * beta0^2) = xi) :
    h *
        (twoLoopStepCubic beta0 beta1 h /
            (twoLoopStepQuadratic beta0 h)^2 - 1) = xi := by
  rw [step_logCounterterm_is_step_independent hbeta0 hh]
  exact hxi

#print axioms twoLoopStepCubic_eq_sq_add
#print axioms step_logCounterterm_is_step_independent
#print axioms step_crossingLogCoeff_is_step_independent
#print axioms step_logCounterterm_transport

end Millennium.YangMills
