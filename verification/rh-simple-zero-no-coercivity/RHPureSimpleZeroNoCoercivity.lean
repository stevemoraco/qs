import Mathlib

namespace RHPureSimpleZeroNoCoercivity

/-!
A finite algebraic obstruction for the positive Selberg companion near a pure
simple-zero principal part. This file proves no analytic statement about zeta
and no form of the Riemann hypothesis.
-/

/-- In the denominator-cleared pure simple-zero model `L = -a`, `L' = a^2`,
the positive companion vanishes and cannot control the nonzero square of `L`. -/
theorem pureSimpleZero_noCoercivity (C a : ℝ) (ha : a ≠ 0) :
    ¬ (|(-a : ℝ)| ^ 2 ≤ C * |(-a : ℝ) ^ 2 - a ^ 2|) := by
  have hpos : 0 < |a| ^ 2 := pow_pos (abs_pos.mpr ha) 2
  simpa [pow_two] using (not_le_of_gt hpos)

/-- Smallest integral witness, corresponding to `z = 1`, `L = -1`, `L' = 1`. -/
theorem pureSimpleZero_zOne (C : ℝ) :
    ¬ (|(-1 : ℝ)| ^ 2 ≤ C * |(-1 : ℝ) ^ 2 - (1 : ℝ) ^ 2|) := by
  exact pureSimpleZero_noCoercivity C 1 one_ne_zero

#print axioms pureSimpleZero_noCoercivity
#print axioms pureSimpleZero_zOne

end RHPureSimpleZeroNoCoercivity
