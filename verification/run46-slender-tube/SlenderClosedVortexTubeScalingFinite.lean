import Mathlib

/-!
# Run46 slender closed-vortex-tube scaling finite core

HONESTY BOUNDARY

This file verifies only finite real exponent algebra used by the Run46
Navier--Stokes candidate-geometry audit:

* the tube-volume exponent;
* the induced L2-amplitude exponent;
* the strain and turnover exponents;
* slenderness and short-wave inequalities in the Palasek window;
* base and child viscous-margin inequalities;
* the exact loss-frontier algebra;
* one explicit construction of admissible `b` and `beta` from a strict
  instability-loss margin.

It does not formalize vortex tubes, Euler or Navier--Stokes solutions,
Floquet theory, thin-ring speed, Fourier localization, nonlinear shadowing,
blowup, regularity, or any official Clay statement.
-/

namespace MillenniumBraid
namespace Run46SlenderTube

/-- Core area exponent plus centerline-length exponent equals the Palasek
intermittent-volume exponent. -/
theorem tube_volume_exponent (alpha : ℝ) :
    (-2 : ℝ) + (4 - 2 * alpha) = -2 * (alpha - 1) := by
  ring

/-- Pointwise velocity exponent plus half the tube-volume exponent equals the
Palasek low-shell L2 exponent. -/
theorem tube_l2_amplitude_exponent (alpha beta : ℝ) :
    (beta - 1) + (-2 * (alpha - 1)) / 2 = beta - alpha := by
  ring

/-- Velocity divided by core radius has exponent `beta`. -/
theorem tube_strain_exponent (beta : ℝ) :
    (beta - 1) + 1 = beta := by
  ring

/-- Core radius divided by velocity has exponent `-beta`. -/
theorem tube_turnover_exponent (beta : ℝ) :
    (-1 : ℝ) - (beta - 1) = -beta := by
  ring

/-- In the upper Palasek alpha window the core-to-length exponent is negative,
so the tube becomes slender. -/
theorem tube_slenderness_exponent_negative
    (alpha : ℝ)
    (hupper : alpha < 5 / 2) :
    2 * alpha - 5 < 0 := by
  nlinarith

/-- The reciprocal slenderness exponent is positive. -/
theorem tube_length_over_core_exponent_positive
    (alpha : ℝ)
    (hupper : alpha < 5 / 2) :
    0 < 5 - 2 * alpha := by
  nlinarith

/-- A child frequency `R^b` supports increasingly many wavelengths around the
closed tube throughout the strict Palasek window. -/
theorem tube_centerline_wavelength_exponent_positive
    (alpha b : ℝ)
    (hb : 1 < b)
    (hupper : alpha < 5 / 2) :
    0 < b + 4 - 2 * alpha := by
  nlinarith

/-- The child wave is short relative to the core whenever `b>1`. -/
theorem tube_core_shortwave_exponent_positive
    (b : ℝ)
    (hb : 1 < b) :
    0 < b - 1 := by
  nlinarith

/-- The Palasek condition `2b<beta`, together with `b>1`, makes core-scale
viscosity negligible on the activation clock. -/
theorem tube_base_viscous_exponent_negative
    (b beta : ℝ)
    (hb : 1 < b)
    (hmargin : 2 * b < beta) :
    2 - beta < 0 := by
  nlinarith

/-- The same source condition makes child-frequency viscosity negligible. -/
theorem tube_child_viscous_exponent_negative
    (b beta : ℝ)
    (hmargin : 2 * b < beta) :
    2 * b - beta < 0 := by
  nlinarith

/-- A loss of `m` powers of slenderness is feasible exactly above the rational
alpha threshold `(2+5m)/(1+2m)`. -/
theorem instability_loss_frontier_iff
    (alpha m : ℝ)
    (hm : 0 ≤ m) :
    m * (5 - 2 * alpha) < alpha - 2 ↔
      (2 + 5 * m) / (1 + 2 * m) < alpha := by
  have hden : 0 < 1 + 2 * m := by
    nlinarith
  constructor
  · intro h
    apply (div_lt_iff₀ hden).2
    nlinarith
  · intro h
    have h' := (div_lt_iff₀ hden).1 h
    nlinarith

/-- Fixed-order ellipticity (`m=0`) is feasible exactly for `alpha>2`. -/
theorem zero_loss_threshold_iff (alpha : ℝ) :
    (0 : ℝ) < alpha - 2 ↔ 2 < alpha := by
  nlinarith

/-- Linear slenderness loss (`m=1`) is feasible exactly for `alpha>7/3`. -/
theorem linear_loss_threshold_iff (alpha : ℝ) :
    5 - 2 * alpha < alpha - 2 ↔ (7 : ℝ) / 3 < alpha := by
  constructor <;> intro h <;> nlinarith

/-- Quadratic slenderness loss (`m=2`) is feasible exactly for `alpha>12/5`. -/
theorem quadratic_loss_threshold_iff (alpha : ℝ) :
    2 * (5 - 2 * alpha) < alpha - 2 ↔ (12 : ℝ) / 5 < alpha := by
  constructor <;> intro h <;> nlinarith

/-- A strict loss frontier produces explicit Palasek parameters. The choices
are `eps = gap/4`, `b = 1+eps`, and `beta = alpha-eps`. -/
theorem explicit_palasek_margin_witness
    (alpha m : ℝ)
    (hm : 0 ≤ m)
    (hupper : alpha < 5 / 2)
    (hfrontier : m * (5 - 2 * alpha) < alpha - 2) :
    let eps := (alpha - 2 - m * (5 - 2 * alpha)) / 4
    let b := 1 + eps
    let beta := alpha - eps
    1 < b ∧
      b < alpha / 2 ∧
      2 * b < beta ∧
      beta < alpha ∧
      m * (5 - 2 * alpha) < beta - 2 * b := by
  dsimp
  have hslender : 0 < 5 - 2 * alpha := by
    nlinarith
  have hmterm : 0 ≤ m * (5 - 2 * alpha) :=
    mul_nonneg hm (le_of_lt hslender)
  have hgap : 0 < alpha - 2 - m * (5 - 2 * alpha) := by
    nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

#print axioms tube_volume_exponent
#print axioms tube_l2_amplitude_exponent
#print axioms tube_strain_exponent
#print axioms tube_turnover_exponent
#print axioms tube_slenderness_exponent_negative
#print axioms tube_length_over_core_exponent_positive
#print axioms tube_centerline_wavelength_exponent_positive
#print axioms tube_core_shortwave_exponent_positive
#print axioms tube_base_viscous_exponent_negative
#print axioms tube_child_viscous_exponent_negative
#print axioms instability_loss_frontier_iff
#print axioms zero_loss_threshold_iff
#print axioms linear_loss_threshold_iff
#print axioms quadratic_loss_threshold_iff
#print axioms explicit_palasek_margin_witness

end Run46SlenderTube
end MillenniumBraid
