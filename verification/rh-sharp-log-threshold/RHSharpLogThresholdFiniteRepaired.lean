import Mathlib

/-!
# RH sharp logarithmic threshold: finite algebraic core

This file formalizes only the real-number algebra behind
`research/rh/RH_SHARP_LOGARITHMIC_PREFIX_RATIO_THRESHOLD_2026-08-13.md`.

It does **not** formalize primes, Chebyshev functions, the explicit formula,
zero counting, the prime number theorem, Johnston's oscillation theorem,
Guth--Maynard short intervals, infinite series, or RH.
-/

namespace RHSharpLogThresholdFinite

/-- A bounded additive error around `L/2` gives the lower quadratic comparison
once the main scale is at least four times the error bound. -/
theorem bounded_half_main_square_lower
    {L R B : ℝ}
    (hB : 0 ≤ B)
    (hL : 4 * B ≤ L)
    (happrox : |R - L / 2| ≤ B) :
    (L / 4) ^ 2 ≤ R ^ 2 := by
  rcases abs_le.mp happrox with ⟨hlow, hupp⟩
  have hL0 : 0 ≤ L := by nlinarith
  have hRlow : L / 4 ≤ R := by nlinarith
  have hR0 : 0 ≤ R := le_trans (by nlinarith) hRlow
  nlinarith

/-- The matching upper quadratic comparison. -/
theorem bounded_half_main_square_upper
    {L R B : ℝ}
    (hB : 0 ≤ B)
    (hL : 4 * B ≤ L)
    (happrox : |R - L / 2| ≤ B) :
    R ^ 2 ≤ (3 * L / 4) ^ 2 := by
  rcases abs_le.mp happrox with ⟨hlow, hupp⟩
  have hL0 : 0 ≤ L := by nlinarith
  have hRlow : L / 4 ≤ R := by nlinarith
  have hR0 : 0 ≤ R := le_trans (by nlinarith) hRlow
  have hRhigh : R ≤ 3 * L / 4 := by nlinarith
  nlinarith

/-- Combined finite comparison corresponding to
`R_p = (1/2) log p + O(1)`. -/
theorem bounded_half_main_square_comparable
    {L R B : ℝ}
    (hB : 0 ≤ B)
    (hL : 4 * B ≤ L)
    (happrox : |R - L / 2| ≤ B) :
    (L / 4) ^ 2 ≤ R ^ 2 ∧
      R ^ 2 ≤ (3 * L / 4) ^ 2 := by
  exact ⟨
    bounded_half_main_square_lower hB hL happrox,
    bounded_half_main_square_upper hB hL happrox
  ⟩

/-- Dividing a logarithmic square by a logarithmic `alpha`-weight leaves the
prime-harmonic exponent `alpha-2`. -/
theorem logarithmic_threshold_shift
    (alpha : ℝ) :
    alpha - 2 = alpha + (-2) := by
  ring

/-- The sharp admissible range has positive residual logarithmic exponent. -/
theorem logarithmic_threshold_positive
    {alpha : ℝ}
    (h : 2 < alpha) :
    0 < alpha - 2 := by
  linarith

/-- At the endpoint `alpha=2`, the residual logarithmic exponent vanishes. -/
theorem logarithmic_threshold_endpoint :
    (2 : ℝ) - 2 = 0 := by
  norm_num

/-- Below the endpoint, the residual exponent is negative. -/
theorem logarithmic_threshold_negative
    {alpha : ℝ}
    (h : alpha < 2) :
    alpha - 2 < 0 := by
  linarith

/-- Exact exponent contributed by a false-RH prime-rich block to any fixed
logarithmically weighted quadratic series. -/
theorem false_rh_block_exponent_identity
    (delta epsilon : ℝ) :
    (1 - epsilon) + (2 * delta - 2 * epsilon) - 1
      = 2 * delta - 3 * epsilon := by
  ring

/-- The false-RH block retains a positive polynomial margin after choosing
`3 epsilon < 2 delta`; every fixed logarithmic power is then negligible at
the analytic layer. -/
theorem false_rh_block_margin
    {delta epsilon : ℝ}
    (h : 3 * epsilon < 2 * delta) :
    0 < 2 * delta - 3 * epsilon := by
  linarith

/-- Exact normalized root identity used to remove the prime power:
`R²/p = 4(theta/p)(1-Q)²`. -/
theorem normalized_root_identity
    {R p theta Q : ℝ}
    (hp : p ≠ 0)
    (hid : R ^ 2 = 4 * theta * (1 - Q) ^ 2) :
    R ^ 2 / p = 4 * (theta / p) * (1 - Q) ^ 2 := by
  rw [hid]
  field_simp [hp]

/-- Abstract logical packaging of the sharpened positive-series criterion. -/
theorem sharp_log_series_criterion
    {P finiteSeries : Prop}
    (hforward : P → finiteSeries)
    (hfalse : ¬ P → ¬ finiteSeries) :
    P ↔ finiteSeries := by
  constructor
  · exact hforward
  · intro hfinite
    by_contra hP
    exact hfalse hP hfinite

#print axioms bounded_half_main_square_lower
#print axioms bounded_half_main_square_upper
#print axioms bounded_half_main_square_comparable
#print axioms logarithmic_threshold_shift
#print axioms logarithmic_threshold_positive
#print axioms logarithmic_threshold_endpoint
#print axioms logarithmic_threshold_negative
#print axioms false_rh_block_exponent_identity
#print axioms false_rh_block_margin
#print axioms normalized_root_identity
#print axioms sharp_log_series_criterion

end RHSharpLogThresholdFinite
