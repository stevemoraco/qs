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

def m : ℝ := 1 / 4

def sigma : ℝ := 1 / 2

def a : ℝ := 1

def M : ℝ := 3

def lambda : ℝ := 1 / (1 - sigma * a)

/-- The local holomorphy cap is satisfied in the counterexample. -/
theorem localHolomorphyGate : sigma * a < 1 := by
  norm_num [sigma, a]

/-- C70B/B3's displayed geometric profile gate passes strictly. -/
theorem printedProfileGate : m * lambda < 1 := by
  norm_num [m, lambda, sigma, a]

/-- B1's unpaid zero-order envelope reverses the geometric conclusion. -/
theorem unpaidZeroOrderRatio : 1 < m * M * lambda := by
  norm_num [m, M, lambda, sigma, a]

/-- The exact size-layer terms used in the paper counterexample. -/
def layerTerm (V : ℕ) : ℝ := 6 * (3 / 2 : ℝ) ^ V

/-- Consecutive size layers grow by the exact factor 3/2. -/
theorem layerTerm_succ (V : ℕ) :
    layerTerm (V + 1) = (3 / 2 : ℝ) * layerTerm V := by
  simp [layerTerm, pow_succ]
  ring

/-- In particular the positive size-layer sequence is strictly increasing. -/
theorem layerTerm_strict_growth (V : ℕ) :
    layerTerm V < layerTerm (V + 1) := by
  rw [layerTerm_succ]
  have hpos : 0 < layerTerm V := by
    positivity
  nlinarith

/-- If the zero-order envelope has already been normalized below one,
then multiplying by it cannot make a nonnegative geometric ratio worse. -/
theorem normalizedZeroOrder_safe
    {m0 M0 lam0 : ℝ}
    (hm0 : 0 ≤ m0)
    (hM0 : 0 ≤ M0)
    (hM1 : M0 ≤ 1)
    (hlam0 : 0 ≤ lam0)
    (hgate : m0 * lam0 < 1) :
    m0 * M0 * lam0 < 1 := by
  have hmul : m0 * M0 ≤ m0 := by
    nlinarith
  have hle : m0 * M0 * lam0 ≤ m0 * lam0 :=
    mul_le_mul_of_nonneg_right hmul hlam0
  exact lt_of_le_of_lt hle hgate

#print axioms localHolomorphyGate
#print axioms printedProfileGate
#print axioms unpaidZeroOrderRatio
#print axioms layerTerm_succ
#print axioms layerTerm_strict_growth
#print axioms normalizedZeroOrder_safe

end YMC70ZeroOrderEnvelopeFirewall
