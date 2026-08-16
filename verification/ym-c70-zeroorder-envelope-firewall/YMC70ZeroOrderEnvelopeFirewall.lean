import Mathlib

/-!
Finite real-algebra firewall for RH #953 / C70B Theorem B3.

The parent local Cauchy bound carries a zero-order factor `M` at every vertex.
This file checks an exact scalar instance where the printed profile gate
`m * lambda < 1` passes but the actual ratio after an unpaid zero-order factor,
`m * M * lambda`, is bigger than one.

It does not formalize Kirk's rooted norm, source trees, convergence of the full
constructive expansion, OS reconstruction, Yang--Mills mass gap, or any Clay
statement.
-/

namespace YMC70ZeroOrderEnvelopeFirewall

/-- The local holomorphy cap is satisfied for sigma=1/2 and a=1. -/
theorem localHolomorphyGate :
    (1 / 2 : ℝ) * 1 < 1 := by
  norm_num

/-- C70B/B3's displayed geometric profile gate passes strictly for m=1/4,
lambda=2. -/
theorem printedProfileGate :
    (1 / 4 : ℝ) * (1 / (1 - (1 / 2 : ℝ) * 1)) < 1 := by
  norm_num

/-- The displayed profile ratio is exactly one half. -/
theorem printedRatio_eq_half :
    (1 / 4 : ℝ) * (1 / (1 - (1 / 2 : ℝ) * 1)) = 1 / 2 := by
  norm_num

/-- B1's unpaid zero-order envelope M=3 reverses the geometric conclusion. -/
theorem unpaidZeroOrderRatio :
    1 < (1 / 4 : ℝ) * 3 * (1 / (1 - (1 / 2 : ℝ) * 1)) := by
  norm_num

/-- The actual size-layer ratio is exactly three halves. -/
theorem actualRatio_eq_threeHalves :
    (1 / 4 : ℝ) * 3 * (1 / (1 - (1 / 2 : ℝ) * 1)) = 3 / 2 := by
  norm_num

/-- If the zero-order envelope has already been normalized below one,
then multiplying by it cannot make a nonnegative geometric ratio worse. -/
theorem normalizedZeroOrder_safe
    {m0 M0 lam0 : ℝ}
    (hm0 : 0 ≤ m0)
    (hM1 : M0 ≤ 1)
    (hlam0 : 0 ≤ lam0)
    (hgate : m0 * lam0 < 1) :
    m0 * M0 * lam0 < 1 := by
  have hmul : m0 * M0 ≤ m0 * 1 :=
    mul_le_mul_of_nonneg_left hM1 hm0
  have hle : m0 * M0 * lam0 ≤ (m0 * 1) * lam0 :=
    mul_le_mul_of_nonneg_right hmul hlam0
  have hle' : m0 * M0 * lam0 ≤ m0 * lam0 := by
    simpa using hle
  exact lt_of_le_of_lt hle' hgate

#print axioms localHolomorphyGate
#print axioms printedProfileGate
#print axioms printedRatio_eq_half
#print axioms unpaidZeroOrderRatio
#print axioms actualRatio_eq_threeHalves
#print axioms normalizedZeroOrder_safe

end YMC70ZeroOrderEnvelopeFirewall
