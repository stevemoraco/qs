import Mathlib

namespace RHNormalizedPrefixRatioFinite

/-- Exact root-to-ratio square identity: if `ratio = 1-root/(2*sqrtTheta)`,
then `root² = 4 theta (1-ratio)²`. The analytic layer supplies the actual
square-root relation and positivity of `theta`. -/
theorem root_ratio_square_identity
    {root theta ratio sqrtTheta : ℝ}
    (hroot : root = 2 * sqrtTheta * (1 - ratio))
    (hsq : sqrtTheta ^ 2 = theta) :
    root ^ 2 = 4 * theta * (1 - ratio) ^ 2 := by
  rw [hroot]
  nlinarith

/-- Abstract lower transfer from a Chebyshev lower bound `c p <= theta`. -/
theorem ratio_energy_lower
    {c p theta ratio root : ℝ}
    (hc : 0 ≤ c)
    (hp : 0 < p)
    (hcheb : c * p ≤ theta)
    (hid : root ^ 2 = 4 * theta * (1 - ratio) ^ 2) :
    4 * c * (1 - ratio) ^ 2 ≤ root ^ 2 / p := by
  have hsq : 0 ≤ (1 - ratio) ^ 2 := sq_nonneg _
  have hmul : 4 * c * p * (1 - ratio) ^ 2 ≤
      4 * theta * (1 - ratio) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcheb hsq]
  rw [hid]
  exact (le_div_iff₀ hp).2 (by nlinarith)

/-- Abstract upper transfer from a Chebyshev upper bound `theta <= C p`. -/
theorem ratio_energy_upper
    {C p theta ratio root : ℝ}
    (hC : 0 ≤ C)
    (hp : 0 < p)
    (hcheb : theta ≤ C * p)
    (hid : root ^ 2 = 4 * theta * (1 - ratio) ^ 2) :
    root ^ 2 / p ≤ 4 * C * (1 - ratio) ^ 2 := by
  have hsq : 0 ≤ (1 - ratio) ^ 2 := sq_nonneg _
  have hmul : 4 * theta * (1 - ratio) ^ 2 ≤
      4 * C * p * (1 - ratio) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcheb hsq]
  rw [hid]
  exact (div_le_iff₀ hp).2 (by nlinarith)

/-- The factorized normalized defect is the product `(1-Q)(1+Q)`. -/
theorem normalized_factorization
    (Q : ℝ) :
    1 - Q ^ 2 = (1 - Q) * (1 + Q) := by
  ring

/-- If `Q` is eventually trapped in a fixed positive compact interval, the
root and factorized normalized defects are two-sided comparable. -/
theorem normalized_factor_upper
    {Q u : ℝ}
    (hQ : |1 + Q| ≤ u)
    (hu : 0 ≤ u) :
    (1 - Q ^ 2) ^ 2 ≤ u ^ 2 * (1 - Q) ^ 2 := by
  rw [normalized_factorization]
  have habs : (1 + Q) ^ 2 ≤ u ^ 2 := by
    nlinarith [sq_nonneg (u - |1 + Q|), sq_abs (1 + Q)]
  have hsq : 0 ≤ (1 - Q) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right habs hsq]

/-- A positive lower bound on `1+Q` gives the reverse comparison. -/
theorem normalized_factor_lower
    {Q l : ℝ}
    (hl : 0 ≤ l)
    (hQ : l ≤ 1 + Q) :
    l ^ 2 * (1 - Q) ^ 2 ≤ (1 - Q ^ 2) ^ 2 := by
  rw [normalized_factorization]
  have hfactor : l ^ 2 ≤ (1 + Q) ^ 2 := by
    nlinarith
  have hsq : 0 ≤ (1 - Q) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hfactor hsq]

/-- Exact false-RH normalized block exponent after the square-root
normalization removes one power of the prime. -/
theorem normalized_block_exponent_identity
    (delta epsilon : ℝ) :
    (1 - epsilon) + (2 * delta - 1 - 2 * epsilon)
      = 2 * delta - 3 * epsilon := by
  ring

/-- The normalized bad-block contribution has positive polynomial growth
whenever `3 epsilon < 2 delta`. -/
theorem normalized_block_margin
    {delta epsilon : ℝ}
    (h : 3 * epsilon < 2 * delta) :
    0 < 2 * delta - 3 * epsilon := by
  linarith

/-- Abstract packaging of the normalized weighted-ell2 criterion. -/
theorem normalized_series_criterion
    {P finiteNormalizedSeries : Prop}
    (hforward : P → finiteNormalizedSeries)
    (hfalse : ¬ P → ¬ finiteNormalizedSeries) :
    P ↔ finiteNormalizedSeries := by
  constructor
  · exact hforward
  · intro hfinite
    by_contra hP
    exact hfalse hP hfinite

#print axioms root_ratio_square_identity
#print axioms ratio_energy_lower
#print axioms ratio_energy_upper
#print axioms normalized_factorization
#print axioms normalized_factor_upper
#print axioms normalized_factor_lower
#print axioms normalized_block_exponent_identity
#print axioms normalized_block_margin
#print axioms normalized_series_criterion

end RHNormalizedPrefixRatioFinite
