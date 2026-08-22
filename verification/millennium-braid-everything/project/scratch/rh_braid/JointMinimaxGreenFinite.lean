import Mathlib

/-!
# Finite bookkeeping core for the RH joint-minimax Green obstruction

The potential-theory and zeta-density estimates enter as hypotheses here.
This file formalizes only the finite inequality layer. It does not prove RH.
-/

namespace RHProof
namespace JointMinimaxGreen

/-- If the listed-zero Green potential beats the worst allowed degree budget,
then the Bernstein--Walsh lower exponent is strictly positive. -/
theorem positive_green_exponent
    (J n gInf sumG : ℝ)
    (hgInf : 0 ≤ gInf)
    (hn : n ≤ 2 * J)
    (hsum : 2 * J * gInf < sumG) :
    0 < -n * gInf + sumG := by
  have hmul : n * gInf ≤ (2 * J) * gInf :=
    mul_le_mul_of_nonneg_right hn hgInf
  nlinarith

/-- Quantitative version with a lower-model Green density `k` and error `eps`. -/
theorem positive_green_exponent_with_error
    (B n gInf k eps sumG : ℝ)
    (hgInf : 0 ≤ gInf)
    (hn : n ≤ B)
    (herror : eps < B * (k - gInf))
    (hsum : B * k - eps ≤ sumG) :
    0 < -n * gInf + sumG := by
  have hmul : n * gInf ≤ B * gInf :=
    mul_le_mul_of_nonneg_right hn hgInf
  have hgap : B * gInf < B * k - eps := by
    nlinarith
  linarith

/-- At critical density the asymptotic margin is positive once the integrated
finite-pole Green contribution strictly dominates the infinity-pole value and
`c ≥ 1`. -/
theorem critical_margin_positive
    (c sK atanhS : ℝ)
    (hc : 1 ≤ c)
    (hsK : 0 < sK)
    (hstrict : atanhS < sK) :
    0 < c * sK - atanhS := by
  have hcsK : sK ≤ c * sK := by
    nlinarith
  linarith

end JointMinimaxGreen
end RHProof
