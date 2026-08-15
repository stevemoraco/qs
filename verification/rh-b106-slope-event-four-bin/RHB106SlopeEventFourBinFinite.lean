import Mathlib

/-!
# RH B106 slope-event four-bin finite core

Finite real algebra only.

This file formalizes the load-bearing algebra behind the B106 reduction of the
exact B46 prime-power channel:

* the five jump sizes of the piecewise-linear Haar autocorrelation derivative;
* the fact that only the two ±h jumps are positive candidates;
* the five-point signed stencil and its exact square-root-main-mode cancellation;
* finite upper-barrier propagation across constant pieces and downward jumps;
* safe absorption of a uniformly bounded proper-prime-power correction.

It deliberately does NOT formalize the von Mangoldt function, prime powers,
Chebyshev/PNT estimates, the explicit formula, Landau's theorem, the B46/B46A
analytic bridge, the Riemann hypothesis, or a Zeta-23/BGST matrix theorem.
No open conclusion is encoded as an axiom or hypothesis carrier.
-/

namespace RHB106SlopeEventFourBinFinite

/-- `1+c+c^2`, the magnitude of the inner B46 slope. -/
def A0 (c : ℝ) : ℝ := 1 + c + c ^ 2

/-- `(1+c)^2`, the exact positive jump at each ±h event. -/
def J (c : ℝ) : ℝ := (1 + c) ^ 2

/-- The exact cumulative five-point derivative stencil. -/
def stencil (c xm2 xm1 x0 xp1 xp2 : ℝ) : ℝ :=
  -c * xm2 + J c * xm1 - 2 * A0 c * x0 + J c * xp1 - c * xp2

/-- The two slope magnitudes add to the positive jump `(1+c)^2`. -/
theorem inner_plus_outer_eq_jump (c : ℝ) :
    A0 c + c = J c := by
  simp [A0, J]
  ring

/-- Outer-left event: slope `0 -> -c`. -/
theorem outer_left_jump (c a : ℝ) :
    (-c * a) - 0 = -c * a := by
  ring

/-- First inner event: slope `-c -> A0`, hence jump `J*a`. -/
theorem left_inner_jump (c a : ℝ) :
    A0 c * a - (-c * a) = J c * a := by
  rw [← inner_plus_outer_eq_jump c]
  ring

/-- Center event: slope `A0 -> -A0`. -/
theorem center_jump (c a : ℝ) :
    (-A0 c * a) - A0 c * a = -2 * A0 c * a := by
  ring

/-- Second inner event: slope `-A0 -> c`, hence jump `J*a`. -/
theorem right_inner_jump (c a : ℝ) :
    c * a - (-A0 c * a) = J c * a := by
  rw [← inner_plus_outer_eq_jump c]
  ring

/-- Outer-right event: slope `c -> 0`. -/
theorem outer_right_jump (c a : ℝ) :
    0 - c * a = -c * a := by
  ring

/-- The complete jump vector is neutral, as required for compact support. -/
theorem jump_vector_sum_zero (c : ℝ) :
    -c + J c - 2 * A0 c + J c - c = 0 := by
  simp [A0, J]
  ring

/-- For positive `c` and positive atom weight, the two inner jumps are strictly positive. -/
theorem inner_jump_positive {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    0 < J c * a := by
  have h1c : 0 < 1 + c := by linarith
  have hJ : 0 < J c := by
    simp [J]
    positivity
  exact mul_pos hJ ha

/-- For nonnegative atom weight, both outer jumps are nonpositive. -/
theorem outer_jump_nonpos {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) :
    -c * a ≤ 0 := by
  exact neg_nonpos.mpr (mul_nonneg hc ha)

/-- For nonnegative atom weight and positive `c`, the central jump is nonpositive. -/
theorem center_jump_nonpos {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) :
    -2 * A0 c * a ≤ 0 := by
  have hA : 0 ≤ A0 c := by
    simp [A0]
    nlinarith [sq_nonneg c]
  have hprod : 0 ≤ 2 * A0 c * a := by positivity
  linarith

/-- Exact polynomial identity killing the square-root main mode of the five-point stencil.

If consecutive scale samples differ by the factor `c=e^(h/2)`, multiplying the
stencil by one harmless `c` leaves exactly this polynomial. -/
theorem square_root_main_mode_cancellation (c : ℝ) :
    -c ^ 4 + J c * c ^ 2 - 2 * A0 c * c + J c - 1 = 0 := by
  simp [A0, J]
  ring

/-- The signed four-bin coefficients sum to zero after rewriting the cumulative stencil. -/
theorem four_bin_coefficient_sum_zero (c : ℝ) :
    c - A0 c + A0 c - c = 0 := by
  ring

/-- On a constant-slope cell, an increasing barrier cannot create a new upper violation. -/
theorem constant_cell_preserves_upper_barrier
    {v b0 b1 : ℝ}
    (hsafe : v ≤ b0) (hbarrier : b0 ≤ b1) :
    v ≤ b1 := by
  exact hsafe.trans hbarrier

/-- A downward event followed by a nondecreasing barrier cannot create a new upper violation. -/
theorem downward_event_preserves_upper_barrier
    {old new b0 b1 : ℝ}
    (hsafe : old ≤ b0)
    (hdown : new ≤ old)
    (hbarrier : b0 ≤ b1) :
    new ≤ b1 := by
  exact hdown.trans (hsafe.trans hbarrier)

/-- Therefore only an upward jump needs a fresh upper-barrier check in the finite event logic. -/
theorem upward_event_check_is_sufficient
    {old new b0 b1 : ℝ}
    (_hsafe : old ≤ b0)
    (_hbarrier : b0 ≤ b1)
    (hnew : new ≤ b1) :
    new ≤ b1 := hnew

/-- A uniformly bounded additive correction can be absorbed by enlarging the upper barrier. -/
theorem bounded_correction_absorbs_into_barrier
    {full primeOnly barrier M : ℝ}
    (hM : 0 ≤ M)
    (herr : |full - primeOnly| ≤ M)
    (hprime : primeOnly ≤ barrier) :
    full ≤ barrier + M := by
  have hup : full - primeOnly ≤ M := (abs_le.mp herr).2
  linarith

/-- Symmetric opposite slopes can cancel exactly while carrying nonzero amplitude.
This is the finite scalar firewall against inferring a value bound from slope geometry alone. -/
theorem symmetric_slope_cancellation (A mass : ℝ) :
    A * mass + (-A) * mass = 0 := by
  ring

#print axioms A0
#print axioms J
#print axioms stencil
#print axioms inner_plus_outer_eq_jump
#print axioms outer_left_jump
#print axioms left_inner_jump
#print axioms center_jump
#print axioms right_inner_jump
#print axioms outer_right_jump
#print axioms jump_vector_sum_zero
#print axioms inner_jump_positive
#print axioms outer_jump_nonpos
#print axioms center_jump_nonpos
#print axioms square_root_main_mode_cancellation
#print axioms four_bin_coefficient_sum_zero
#print axioms constant_cell_preserves_upper_barrier
#print axioms downward_event_preserves_upper_barrier
#print axioms upward_event_check_is_sufficient
#print axioms bounded_correction_absorbs_into_barrier
#print axioms symmetric_slope_cancellation

end RHB106SlopeEventFourBinFinite
