import Mathlib

namespace NSWKBDiagonalBudgetFinite

/-- Finite logarithmic core of the WKB diagonal theorem.

One quarter of the depth gain pays the corrector constant, one half pays the
fixed derivative/prefactor exponent, and the remaining quarter gives decay.
The shell sequence, factorial estimates, packet construction, and NSE are
intentionally absent. -/
theorem diagonal_log_budget
    {constantCost fixedCost gain depth logN : ℝ}
    (hlogN : 0 ≤ logN)
    (hconstant : constantCost ≤ gain * depth * logN / 4)
    (hfixed : fixedCost ≤ gain * depth / 2) :
    constantCost + (fixedCost - gain * depth) * logN
      ≤ -(gain * depth * logN) / 4 := by
  have hfixedScaled :
      fixedCost * logN ≤ (gain * depth / 2) * logN :=
    mul_le_mul_of_nonneg_right hfixed hlogN
  nlinarith

/-- Adding an actual residual logarithm below the formal cost preserves the
same quarter-gain upper bound. -/
theorem residual_log_decay
    {logResidual constantCost fixedCost gain depth logN : ℝ}
    (hresidual :
      logResidual ≤ constantCost + (fixedCost - gain * depth) * logN)
    (hlogN : 0 ≤ logN)
    (hconstant : constantCost ≤ gain * depth * logN / 4)
    (hfixed : fixedCost ≤ gain * depth / 2) :
    logResidual ≤ -(gain * depth * logN) / 4 := by
  exact le_trans hresidual
    (diagonal_log_budget hlogN hconstant hfixed)

/-- At the audited packet point, the WKB gain is `1/6`; the surviving decay
budget is therefore exactly `depth * logN / 24`. -/
theorem sixth_gain_log_budget
    {constantCost fixedCost depth logN : ℝ}
    (hlogN : 0 ≤ logN)
    (hconstant : constantCost ≤ depth * logN / 24)
    (hfixed : fixedCost ≤ depth / 12) :
    constantCost + (fixedCost - depth / 6) * logN
      ≤ -(depth * logN) / 24 := by
  have hconstant' :
      constantCost ≤ (1 / 6 : ℝ) * depth * logN / 4 := by
    nlinarith
  have hfixed' : fixedCost ≤ (1 / 6 : ℝ) * depth / 2 := by
    nlinarith
  have h := diagonal_log_budget
    (gain := (1 / 6 : ℝ)) (depth := depth) (logN := logN)
    hlogN hconstant' hfixed'
  nlinarith

/-- The exact rational-point specialization with diagonal depth `k`. -/
theorem rational_packet_diagonal_decay
    {logResidual constantCost fixedCost k logN : ℝ}
    (hresidual :
      logResidual ≤ constantCost + (fixedCost - k / 6) * logN)
    (hlogN : 0 ≤ logN)
    (hconstant : constantCost ≤ k * logN / 24)
    (hfixed : fixedCost ≤ k / 12) :
    logResidual ≤ -(k * logN) / 24 := by
  exact le_trans hresidual
    (sixth_gain_log_budget hlogN hconstant hfixed)

#print axioms diagonal_log_budget
#print axioms residual_log_decay
#print axioms sixth_gain_log_budget
#print axioms rational_packet_diagonal_decay

end NSWKBDiagonalBudgetFinite
