import Mathlib

/-!
# Finite algebra for Chebyshev-amplified centered-difference RH detectors

This file records only scalar algebra/order cores from
`CHEBYSHEV_AMPLIFIED_FINITE_DIFFERENCE_EXTERIOR_2026-08-11.md` and the
adversarial `l1`-cost correction.  It does not formalize the zero sum,
Chebyshev alternation theorem, explicit formula, exponential-type argument,
or any implication to RH.
-/

namespace RHProof
namespace ChebyshevAmplifiedFiniteDifference

/-- Multiplying a nonnegative real-spectrum weight by an attenuation factor in
`[0,1]` preserves nonnegativity and cannot enlarge that weight. -/
theorem attenuated_real_weight
    (j r : ℝ) (hj : 0 ≤ j) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ j * r ∧ j * r ≤ j := by
  constructor
  · exact mul_nonneg hj hr0
  · simpa using mul_le_mul_of_nonneg_left hr1 hj

/-- Abstract strict reflected sign for a Chebyshev-amplified centered
finite-difference atom.  In the analytic application `s = sinh (h*y)` and
`c = cosh (n*h*y)`, so both nonvanishing hypotheses hold for `y ≠ 0`. -/
theorem reflected_weight_strictly_negative
    (mass norm s c h : ℝ)
    (hmass : 0 < mass) (hnorm : 0 < norm)
    (hs : s ≠ 0) (hc : c ≠ 0) (hh : 0 < h) :
    -4 * mass^2 * norm^4 * s^2 * c^2 / h^2 < 0 := by
  have hs2 : 0 < s^2 := sq_pos_of_ne_zero hs
  have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  positivity

/-- Exact factorization behind the first strict improvement (`n = 2`, three
substeps, total radius `3h`). -/
theorem three_substep_gain_identity (s : ℝ) :
    9 * s^2 * (1 + 2 * s^2)^2 - (3 * s + 4 * s^3)^2 =
      4 * s^4 * (5 * s^2 + 3) := by
  ring

/-- The seven-window three-substep reflected amplitude is strictly larger than
the single outer centered-step amplitude for every nonzero hyperbolic sine
parameter. -/
theorem three_substep_strict_gain (s : ℝ) (hs : s ≠ 0) :
    (3 * s + 4 * s^3)^2 < 9 * s^2 * (1 + 2 * s^2)^2 := by
  apply sub_pos.mp
  rw [three_substep_gain_identity]
  have hs2 : 0 < s^2 := sq_pos_of_ne_zero hs
  positivity

/-- Exact algebra behind the cost-normalized correction.  The seven-window
stencil has nine times the `l1` coefficient cost of the outer three-window
stencil at the same total translation radius. -/
theorem three_substep_cost_gap_identity (s : ℝ) :
    9 * (3 * s + 4 * s^3)^2 - 9 * s^2 * (1 + 2 * s^2)^2 =
      36 * s^2 * (2 + 5 * s^2 + 3 * s^4) := by
  ring

/-- Although the seven-window detector has a raw reflected gain, that gain is
strictly smaller than its factor-nine increase in absolute stencil cost. -/
theorem three_substep_gain_below_l1_cost (s : ℝ) (hs : s ≠ 0) :
    9 * s^2 * (1 + 2 * s^2)^2 < 9 * (3 * s + 4 * s^3)^2 := by
  apply sub_pos.mp
  rw [three_substep_cost_gap_identity]
  have hs2 : 0 < s^2 := sq_pos_of_ne_zero hs
  positivity

/-- The generic distinct-frequency amplified stencil has absolute coefficient
sum four before multiplication by `h⁻²`. -/
theorem amplified_stencil_l1_coefficient :
    |(1 : ℝ)| + |(1 : ℝ)| + |(-1 : ℝ)| + |(-1 / 2 : ℝ)| + |(-1 / 2 : ℝ)| = 4 := by
  norm_num

/-- The outer centered-difference stencil also has absolute coefficient sum
four before multiplication by `H⁻²`. -/
theorem outer_stencil_l1_coefficient :
    |(2 : ℝ)| + |(-1 : ℝ)| + |(-1 : ℝ)| = 4 := by
  norm_num

/-- The real-side normalization is essential: once `X > 1`, increasing the
coefficient of `(X-1)^2` strictly increases the off-interval value while
leaving the value at `X=1` fixed. -/
theorem no_ceiling_monotone_growth
    (X A B : ℝ) (hX : 1 < X) (hAB : A < B) :
    1 + A * (X - 1)^2 < 1 + B * (X - 1)^2 := by
  have hx2 : 0 < (X - 1)^2 := sq_pos_of_pos (sub_pos.mpr hX)
  nlinarith

/-- The generic distinct-frequency stencil has zero total coefficient, as a
second-difference multiplier must.  The coefficients are center `1`, the
`±nh` pair totaling `1`, the `±h` pair totaling `-1`, and the two outer pairs
totaling `-1`. -/
theorem stencil_total_coefficient_zero :
    (1 : ℝ) + 1 - 1 - 1 = 0 := by
  norm_num

/-- A positive gain and a positive squared channel norm retain strict
negativity when attached to the reflected atom. -/
theorem negative_after_positive_gain
    (q gain : ℝ) (hq : q < 0) (hgain : 0 < gain) :
    q * gain < 0 := by
  exact mul_neg_of_neg_of_pos hq hgain

end ChebyshevAmplifiedFiniteDifference
end RHProof
