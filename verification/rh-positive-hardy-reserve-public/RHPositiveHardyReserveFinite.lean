import Mathlib

namespace RHPositiveHardyReserveFinite

/-- Finite scalar shell for an endpoint-minus-history Hardy margin.  The analytic
integrals, primes, zeta zeros, and Johnston theorems are deliberately absent. -/
def hardyMargin (boundary endpoint history : ℝ) : ℝ :=
  boundary * endpoint - history

/-- Separating a weighted history into its constant-endpoint contribution and a
signed drawdown leaves a fixed boundary cushion minus that drawdown. -/
theorem drawdown_decomposition
    {boundary base endpoint history drawdown : ℝ}
    (hhistory : history = (boundary - base) * endpoint + drawdown) :
    hardyMargin boundary endpoint history =
      base * endpoint - drawdown := by
  unfold hardyMargin
  rw [hhistory]
  ring

/-- Positivity of the Hardy margin is exactly the strict drawdown budget after
the constant endpoint contribution has been split off. -/
theorem drawdown_budget_iff
    {boundary base endpoint history drawdown : ℝ}
    (hhistory : history = (boundary - base) * endpoint + drawdown) :
    0 < hardyMargin boundary endpoint history ↔
      drawdown < base * endpoint := by
  rw [drawdown_decomposition hhistory]
  linarith

/-- A constant history profile leaves only the boundary cushion. -/
theorem constant_profile_margin
    {boundary base endpoint history : ℝ}
    (hhistory : history = (boundary - base) * endpoint) :
    hardyMargin boundary endpoint history = base * endpoint := by
  unfold hardyMargin
  rw [hhistory]
  ring

/-- Scaled finite shell of the critical half-order formula
`M = base*endpoint/2 - signedDrawdown/4`. -/
def halfOrderMargin (base endpoint signedDrawdown : ℝ) : ℝ :=
  base * endpoint / 2 - signedDrawdown / 4

/-- Exact critical half-order budget. -/
theorem half_order_budget_iff
    {base endpoint signedDrawdown : ℝ} :
    0 < halfOrderMargin base endpoint signedDrawdown ↔
      signedDrawdown < 2 * base * endpoint := by
  unfold halfOrderMargin
  constructor <;> intro h <;> linarith

/-- A positive majorant for the signed drawdown is a valid sufficient route, but
it is strictly stronger than controlling the signed quantity itself. -/
theorem signed_drawdown_majorant_sufficient
    {base endpoint signedDrawdown positiveMajorant : ℝ}
    (hmajor : signedDrawdown ≤ positiveMajorant)
    (hbudget : positiveMajorant < 2 * base * endpoint) :
    0 < halfOrderMargin base endpoint signedDrawdown := by
  rw [half_order_budget_iff]
  linarith

/-- Positivity of the endpoint and boundary cushion alone cannot force the
half-order margin: an admissible positive drawdown can overwhelm both. -/
theorem positive_endpoint_alone_insufficient
    {base endpoint : ℝ}
    (hbase : 0 < base) (hendpoint : 0 < endpoint) :
    halfOrderMargin base endpoint (4 * base * endpoint) < 0 := by
  have hprod : 0 < base * endpoint := mul_pos hbase hendpoint
  unfold halfOrderMargin
  nlinarith

/-- Algebraic right-hand side of the causal exponential-filter ODE. -/
def filterDerivative (alpha signal average : ℝ) : ℝ :=
  alpha * (signal - average)

/-- For positive filter order, strict growth of the causal state is equivalent
to the signal lying strictly above its moving average. -/
theorem filter_derivative_pos_iff
    {alpha signal average : ℝ}
    (halpha : 0 < alpha) :
    0 < filterDerivative alpha signal average ↔ average < signal := by
  unfold filterDerivative
  constructor
  · intro hderiv
    by_contra hnot
    have hle : signal ≤ average := le_of_not_gt hnot
    have hdiff : signal - average ≤ 0 := sub_nonpos.mpr hle
    have hnonpos : alpha * (signal - average) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt halpha) hdiff
    linarith
  · intro hsignal
    exact mul_pos halpha (sub_pos.mpr hsignal)

/-- Horizontal growth exponent of one weighted zero mode. -/
def modeExponent (beta c : ℝ) : ℝ :=
  beta + 1 - c

/-- A weighted mode grows exactly when the weight exponent lies below
`1 + beta`. -/
theorem mode_growth_iff
    {beta c : ℝ} :
    0 < modeExponent beta c ↔ c < 1 + beta := by
  unfold modeExponent
  linarith

/-- At the critical weight `c=3/2`, every mode strictly to the right of the
critical line has positive growth exponent. -/
theorem critical_half_order_detects_offline
    {beta : ℝ} (hbeta : 1 / 2 < beta) :
    0 < modeExponent beta (3 / 2) := by
  unfold modeExponent
  norm_num at hbeta ⊢
  linarith

/-- At the unconditional endpoint weight `c=2`, every nontrivial mode with
`beta<1` is damped. -/
theorem c_two_damps_nontrivial_mode
    {beta : ℝ} (hbeta : beta < 1) :
    modeExponent beta 2 < 0 := by
  unfold modeExponent
  linarith

/-- Nonpositive growth at weight `c` forces the corresponding horizontal-depth
bound. -/
theorem no_growth_implies_depth_bound
    {omega c : ℝ}
    (hgrowth : modeExponent omega c ≤ 0) :
    omega ≤ c - 1 := by
  unfold modeExponent at hgrowth
  linarith

/-- In Hardy-order coordinates `c=2-alpha`, nonpositive growth forces
`omega ≤ 1-alpha`. -/
theorem hardy_order_depth_bound
    {omega alpha : ℝ}
    (hgrowth : modeExponent omega (2 - alpha) ≤ 0) :
    omega ≤ 1 - alpha := by
  unfold modeExponent at hgrowth
  linarith

#print axioms drawdown_decomposition
#print axioms drawdown_budget_iff
#print axioms constant_profile_margin
#print axioms half_order_budget_iff
#print axioms signed_drawdown_majorant_sufficient
#print axioms positive_endpoint_alone_insufficient
#print axioms filter_derivative_pos_iff
#print axioms mode_growth_iff
#print axioms critical_half_order_detects_offline
#print axioms c_two_damps_nontrivial_mode
#print axioms no_growth_implies_depth_bound
#print axioms hardy_order_depth_bound

end RHPositiveHardyReserveFinite
