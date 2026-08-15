import Mathlib

namespace RHB125SelbergPencilFinite

/-!
# RH B125 finite Selberg-scale / Hankel-pencil core

Finite real/rational algebra only.

This file formalizes only the exponent ledgers behind the B125 critical
short-interval reduction and the two-dimensional trace/determinant algebra behind
the B125A range-compressed Hankel pencil.

It deliberately does **not** formalize primes, Chebyshev functions, Selberg
integrals, prime-gap moment interpolation, contour integrals, generalized matrix
eigenvalue theory, zeta/Xi zeros, RH, or its negation.
-/

/-- The B125 critical physical exponent `h = 1 - 1/(2p)` satisfies
`p*h = p - 1/2`. -/
theorem critical_selberg_scale_exponent
    {p : ℝ} (hp : p ≠ 0) :
    p * (1 - 1 / (2 * p)) = p - 1 / 2 := by
  field_simp [hp]
  ring

/-- At the critical scale, a power-mode increment with state exponent `beta`
has short-interval moment exponent `p*beta + 1/2`. -/
theorem critical_mode_moment_exponent
    {p beta : ℝ} (hp : p ≠ 0) :
    p * (1 - 1 / (2 * p)) + p * beta - p + 1 =
      p * beta + 1 / 2 := by
  field_simp [hp]
  ring

/-- The critical state exponent `beta = 1 - 1/(2p)` makes the B125 mode
moment exponent exactly `p`. -/
theorem critical_mode_hits_p
    {p : ℝ} (hp : p ≠ 0) :
    p * (1 - 1 / (2 * p)) + 1 / 2 = p := by
  field_simp [hp]
  ring

/-- For every `p>1`, the proper-prime-power short-interval debt exponent
`p/2 + 1/2` lies strictly below the critical `p` exponent. -/
theorem proper_power_increment_exponent_subcritical
    {p : ℝ} (hp : 1 < p) :
    p / 2 + 1 / 2 < p := by
  linarith

/-- For every `p>1`, the prime-grid discretization exponent obtained from
interpolating first and cubic gap moments is strictly below the B123/B124
normalization exponent `p+1/2`. -/
theorem cubic_gap_discretization_exponent_subcritical
    {p : ℝ} (hp : 1 < p) :
    1 + p / 2 < p + 1 / 2 := by
  linarith

/-- Rewriting the critical state exponent in the fixed-strip variable
`p=q/(q-1)` gives `1/2+1/(2q)`. -/
theorem critical_state_exponent_in_q
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    1 - 1 / (2 * (q / (q - 1))) = 1 / 2 + 1 / (2 * q) := by
  field_simp [hq0, hq1]
  ring

/-- First rung: `q=2`, `p=2` gives the critical physical scale exponent `3/4`. -/
theorem first_rung_scale :
    (1 : ℚ) - 1 / (2 * 2) = 3 / 4 := by
  norm_num

/-- First rung: a beta=3/4 deterministic mode at H=X^(3/4) has quadratic
short-interval moment exponent exactly 2. -/
theorem first_rung_mode_exponent :
    (2 : ℚ) * (3 / 4) + 1 / 2 = 2 := by
  norm_num

/-- Trace of the realified source pencil block `J*K = [[a,-b],[b,a]]`. -/
def pencilTrace (a : ℝ) : ℝ := 2 * a

/-- Determinant of the same block. -/
def pencilDet (a b : ℝ) : ℝ := a ^ 2 + b ^ 2

/-- The characteristic discriminant of one realified conjugate-pair pencil
is exactly `-4 b^2`. -/
theorem pencil_discriminant (a b : ℝ) :
    pencilTrace a ^ 2 - 4 * pencilDet a b = -4 * b ^ 2 := by
  unfold pencilTrace pencilDet
  ring

/-- A scalar strip detector built from the pencil discriminant factors as
`4(delta^2-b^2)`. -/
def pencilStripDetector (delta a b : ℝ) : ℝ :=
  4 * delta ^ 2 + (pencilTrace a ^ 2 - 4 * pencilDet a b)

theorem pencil_strip_detector_factorization (delta a b : ℝ) :
    pencilStripDetector delta a b = 4 * (delta ^ 2 - b ^ 2) := by
  unfold pencilStripDetector
  rw [pencil_discriminant]
  ring

/-- If the source displacement lies inside `[-delta,delta]`, the scalar pencil
strip detector is nonnegative. -/
theorem pencil_strip_detector_nonneg
    {delta a b : ℝ} (hdelta : 0 ≤ delta)
    (hlo : -delta ≤ b) (hhi : b ≤ delta) :
    0 ≤ pencilStripDetector delta a b := by
  rw [pencil_strip_detector_factorization]
  have h1 : 0 ≤ delta - b := sub_nonneg.mpr hhi
  have h2 : 0 ≤ delta + b := by linarith
  have hprod : 0 ≤ (delta - b) * (delta + b) := mul_nonneg h1 h2
  nlinarith

/-- Crossing above the positive strip threshold makes the scalar pencil detector
strictly negative. -/
theorem pencil_strip_detector_negative_of_above
    {delta a b : ℝ} (hdelta : 0 ≤ delta) (h : delta < b) :
    pencilStripDetector delta a b < 0 := by
  rw [pencil_strip_detector_factorization]
  have h1 : 0 < b - delta := sub_pos.mpr h
  have h2 : 0 < b + delta := by linarith
  have hprod : 0 < (b - delta) * (b + delta) := mul_pos h1 h2
  nlinarith

#print axioms critical_selberg_scale_exponent
#print axioms critical_mode_moment_exponent
#print axioms critical_mode_hits_p
#print axioms proper_power_increment_exponent_subcritical
#print axioms cubic_gap_discretization_exponent_subcritical
#print axioms critical_state_exponent_in_q
#print axioms first_rung_scale
#print axioms first_rung_mode_exponent
#print axioms pencilTrace
#print axioms pencilDet
#print axioms pencil_discriminant
#print axioms pencilStripDetector
#print axioms pencil_strip_detector_factorization
#print axioms pencil_strip_detector_nonneg
#print axioms pencil_strip_detector_negative_of_above

end RHB125SelbergPencilFinite
