import Mathlib

/-!
# RH integer-refinement transfer: finite scalar core

Honesty status: this file formalizes only the finite weighted Jensen inequality
for the one-step eighth-order dyadic low-pass mask and the scalar exponent
budget used after the analytic transfer theorem has already been proved.

It does not formalize box functions, convolution, distributions, the von
Mangoldt measure, the prime statistic, the PNT error theorem, the boundary
energy abscissa, the Riemann zeta function, or RH.
-/

namespace MillenniumBraid
namespace RHIntegerRefinementFinite

/-- The eighth-order dyadic refinement mask has total weight `2^8 = 256`. -/
theorem binomialEightWeightSum :
    (1 : ℤ) + 8 + 28 + 56 + 70 + 56 + 28 + 8 + 1 = 256 := by
  norm_num

/-
Finite weighted Jensen inequality for the exact low-pass mask
`(1,8,28,56,70,56,28,8,1)/256`.

The larger heartbeat allowance is computational only: `nlinarith` expands one
exact nonnegative weighted-variance expression. It adds no hypothesis.
-/
set_option maxHeartbeats 1000000 in
theorem binomialEightJensen
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) :
    ((x0 + 8*x1 + 28*x2 + 56*x3 + 70*x4 +
        56*x5 + 28*x6 + 8*x7 + x8) / 256)^2
      ≤
    (x0^2 + 8*x1^2 + 28*x2^2 + 56*x3^2 + 70*x4^2 +
        56*x5^2 + 28*x6^2 + 8*x7^2 + x8^2) / 256 := by
  let μ : ℝ :=
    (x0 + 8*x1 + 28*x2 + 56*x3 + 70*x4 +
      56*x5 + 28*x6 + 8*x7 + x8) / 256
  have hvar :
      0 ≤ (x0 - μ)^2 + 8*(x1 - μ)^2 + 28*(x2 - μ)^2 +
        56*(x3 - μ)^2 + 70*(x4 - μ)^2 + 56*(x5 - μ)^2 +
        28*(x6 - μ)^2 + 8*(x7 - μ)^2 + (x8 - μ)^2 := by
    positivity
  dsimp [μ] at hvar ⊢
  nlinarith

/-- A zero fine-scale exponential budget forces zero horizontal depth. -/
theorem zeroExponentClosesDepth
    (theta : ℝ)
    (htheta : 0 ≤ theta)
    (htransfer : 2 * theta ≤ 0) :
    theta = 0 := by
  linarith

/-- The exact scalar direction of the quantitative exponent transfer. -/
theorem exponentTransfer
    (theta lambda : ℝ)
    (htransfer : 2 * theta ≤ lambda) :
    theta ≤ lambda / 2 := by
  linarith

/--
If a fine estimate has residual exponential rate `gamma` and reciprocal-width
loss `A * alpha`, the transferred horizontal depth is at most half their sum.
-/
theorem polynomialWidthPhaseBudget
    (theta gamma A alpha : ℝ)
    (htransfer : 2 * theta ≤ gamma + A * alpha) :
    theta ≤ (gamma + A * alpha) / 2 := by
  linarith

/-- Fixed-power interval specialization `alpha = 1 - intervalExponent`. -/
theorem fixedPowerPhaseBudget
    (theta gamma A intervalExponent : ℝ)
    (htransfer :
      2 * theta ≤ gamma + A * (1 - intervalExponent)) :
    theta ≤ (gamma + A * (1 - intervalExponent)) / 2 := by
  linarith

#print axioms binomialEightWeightSum
#print axioms binomialEightJensen
#print axioms zeroExponentClosesDepth
#print axioms exponentTransfer
#print axioms polynomialWidthPhaseBudget
#print axioms fixedPowerPhaseBudget

end RHIntegerRefinementFinite
end MillenniumBraid
