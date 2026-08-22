import Mathlib

namespace RHPrimeRootReduction

/-- Normalized difference between the full-knot positive jump and the subsequent
half-odd negative jump, after removing the positive factor
`log p * p^(-2m)`. -/
def compensationBracket (p mroot : ℝ) : ℝ := mroot - 2 - 2 / p

/-- The algebraic compensation criterion. In the arithmetic application
`mroot = p^(m/2)` and `p>0`. -/
theorem compensation_nonnegative
    {p mroot : ℝ}
    (hp : 0 < p)
    (h : 2 + 2 / p ≤ mroot) :
    0 ≤ compensationBracket p mroot := by
  dsimp [compensationBracket]
  linarith

/-- Multiplying a nonnegative compensation bracket by the positive common
prime-power factor preserves nonnegativity. -/
theorem weighted_compensation_nonnegative
    {L w p mroot : ℝ}
    (hL : 0 ≤ L)
    (hw : 0 ≤ w)
    (hp : 0 < p)
    (h : 2 + 2 / p ≤ mroot) :
    0 ≤ L * w * compensationBracket p mroot := by
  have hb : 0 ≤ compensationBracket p mroot :=
    compensation_nonnegative hp h
  positivity

/-- For primes at least 7, the first exponent already clears the compensation
threshold once one has the elementary arithmetic input `sqrt p ≥ 2+2/p`.
This theorem intentionally isolates that arithmetic input instead of hiding it. -/
theorem all_higher_exponents_from_first
    {p r r' : ℝ}
    (hp : 0 < p)
    (hfirst : 2 + 2 / p ≤ r)
    (hmono : r ≤ r') :
    0 ≤ compensationBracket p r' := by
  apply compensation_nonnegative hp
  exact le_trans hfirst hmono

/-- Exact finite checks used by the human classification. -/
theorem p3_m2_clears : (2 : ℝ) + 2 / 3 ≤ 3 := by norm_num

theorem p5_m2_clears : (2 : ℝ) + 2 / 5 ≤ 5 := by norm_num

theorem p2_m4_clears : (2 : ℝ) + 2 / 2 ≤ 4 := by norm_num

/-- The three representative low-scale failures really fail. -/
theorem p2_m2_fails : (2 : ℝ) < 2 + 2 / 2 := by norm_num

theorem p3_m1_squared_firewall : (3 : ℝ) < (2 + 2 / 3)^2 := by norm_num

theorem p5_m1_squared_firewall : (5 : ℝ) < (2 + 2 / 5)^2 := by norm_num

/-- Abstract causal pairing: if a slope receives a positive jump `J`, then a
nonnegative smooth increment `C`, then a negative jump of magnitude `H`, and
`H ≤ J`, the final slope cannot lie below the pre-pair slope. -/
theorem causal_pair_cannot_lower
    {s J C H : ℝ}
    (hJ : 0 ≤ J)
    (hC : 0 ≤ C)
    (hHJ : H ≤ J) :
    s ≤ s + J + C - H := by
  linarith

#print axioms compensation_nonnegative
#print axioms weighted_compensation_nonnegative
#print axioms all_higher_exponents_from_first
#print axioms p3_m2_clears
#print axioms p5_m2_clears
#print axioms p2_m4_clears
#print axioms p2_m2_fails
#print axioms p3_m1_squared_firewall
#print axioms p5_m1_squared_firewall
#print axioms causal_pair_cannot_lower

end RHPrimeRootReduction
