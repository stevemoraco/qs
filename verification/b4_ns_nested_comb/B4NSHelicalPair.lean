import Mathlib

namespace B4NSHelicalPair

/-- Polynomial core of a norm lower bound for the explicit same-helicity
    low-output pair `p=(n,n,0)`, `q=(1-n,-n,0)`. -/
theorem desiredChannelPolynomialMargin {n : ℝ} (hn : 1 ≤ n) :
    2 * (2 * n - 1)^2 ≥ 2 * n^2 - 2 * n + 1 := by
  have hn0 : 0 ≤ n := by linarith
  have hnm1 : 0 ≤ n - 1 := by linarith
  have hprod : 0 ≤ n * (n - 1) := mul_nonneg hn0 hnm1
  nlinarith

/-- Stronger polynomial core for projection onto the positive-helicity parent
    mode at output `(1,0,0)`.  It yields a `K/4` coefficient floor after
    substituting `t^2=2n^2-2n+1`. -/
theorem desiredParentHelicityPolynomialMargin {n : ℝ} (hn : 1 ≤ n) :
    (2 * n - 1)^2 ≥ 2 * n^2 - 2 * n + 1 := by
  have hn0 : 0 ≤ n := by linarith
  have hnm1 : 0 ≤ n - 1 := by linarith
  have hprod : 0 ≤ n * (n - 1) := mul_nonneg hn0 hnm1
  nlinarith

/-- Square-root-free transfer of the preceding polynomial margin. -/
theorem desiredParentHelicityRootMargin
    {n t : ℝ}
    (hn : 1 ≤ n)
    (ht : 0 ≤ t)
    (htsq : t^2 = 2 * n^2 - 2 * n + 1) :
    t ≤ 2 * n - 1 := by
  have hright : 0 ≤ 2 * n - 1 := by linarith
  have hsq := desiredParentHelicityPolynomialMargin hn
  nlinarith

/-- Cross-multiplied form of the positive-helicity coefficient floor.  In the
    explicit vector formula the additional term is `sqrt(2)n-t ≥ 0`. -/
theorem desiredParentHelicityCrossMultiplied
    {K n t extra : ℝ}
    (hK : 0 ≤ K)
    (hn : 1 ≤ n)
    (ht : 0 ≤ t)
    (htsq : t^2 = 2 * n^2 - 2 * n + 1)
    (hExtra : 0 ≤ extra) :
    K * t ≤ K * ((2 * n - 1) + extra) := by
  have hroot := desiredParentHelicityRootMargin hn ht htsq
  exact mul_le_mul_of_nonneg_left (le_trans hroot (by linarith)) hK

/-- The squared child radius denominator dominates `n^2`, yielding the
    angular factor `O(1/n)` for the undesired conjugate high output. -/
theorem angularDenominatorDominatesSquare (n : ℝ) :
    n^2 ≤ 2 * n^2 - 2 * n + 1 := by
  nlinarith [sq_nonneg (n - 1)]

/-- The radial eigenvalue split of the explicit pair has positive numerator. -/
theorem radialSplitNumeratorPositive {n : ℝ} (hn : 1 ≤ n) :
    0 < 2 * n - 1 := by
  linarith

/-- If the desired coefficient is at least `K/4` and leakage is at most
    `K/n`, then the dimensionless leakage ratio is at most `4/n` in
    cross-multiplied form.  No division by the desired coefficient is hidden. -/
theorem relativeLeakageCrossMultiplied
    {desired leakage K n : ℝ}
    (hn : 0 < n)
    (hDesired : K / 4 ≤ desired)
    (hLeakage : leakage ≤ K / n) :
    leakage * n ≤ 4 * desired := by
  have hLeakScaled : leakage * n ≤ K := (le_div_iff₀ hn).mp hLeakage
  have hDesiredScaled : K ≤ 4 * desired := by linarith
  exact le_trans hLeakScaled hDesiredScaled

/-- A relative leakage bound `4/n` can be made smaller than any positive
    trapping margin by taking the scale ratio parameter large enough. -/
theorem leakageBelowAnyMargin
    {margin n : ℝ}
    (hMargin : 0 < margin)
    (hLarge : 4 / margin < n) :
    4 / n < margin := by
  have hn : 0 < n := lt_trans (by positivity : 0 < 4 / margin) hLarge
  rw [div_lt_iff₀ hn]
  have hEquivalent : 4 < margin * n := by
    have := (div_lt_iff₀ hMargin).mp hLarge
    nlinarith
  nlinarith

/-- Exact skew pairing of a desired low-output term and its high-shell
    feedback partner. -/
theorem pairedTransferEnergySkew (c X Y : ℝ) :
    X * (-c * Y^2) + Y * (c * X * Y) = 0 := by
  ring

#print axioms desiredChannelPolynomialMargin
#print axioms desiredParentHelicityPolynomialMargin
#print axioms desiredParentHelicityRootMargin
#print axioms desiredParentHelicityCrossMultiplied
#print axioms angularDenominatorDominatesSquare
#print axioms radialSplitNumeratorPositive
#print axioms relativeLeakageCrossMultiplied
#print axioms leakageBelowAnyMargin
#print axioms pairedTransferEnergySkew

end B4NSHelicalPair
