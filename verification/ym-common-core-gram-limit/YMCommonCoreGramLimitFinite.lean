import Mathlib

/-!
# Yang--Mills common-core Gram-limit finite firewalls

This file formalizes only elementary real-algebraic pieces used in the
common-core one-time OS Gram limit theorem and its counterexamples.

It does not formalize sesquilinear forms, Riesz representation, Hilbert-space
completion, Osterwalder--Schrader reconstruction, self-adjoint semigroups,
lattice gauge theory, continuum limits, or Yang--Mills.
-/

namespace MillenniumBraid
namespace YMCommonCoreGramLimitFinite

/-- Quantitative finite shadow of passing a contraction inequality through a
limit.  If `a,b` are `ε`-close to `A,B` and `b ≤ q a`, then the limiting
inequality has defect at most `(q+1)ε`. -/
theorem approximate_contraction_transfer
    (a b A B q ε : ℝ)
    (hq : 0 ≤ q)
    (hε : 0 ≤ ε)
    (ha : |a - A| ≤ ε)
    (hb : |b - B| ≤ ε)
    (hcontract : b ≤ q * a) :
    B ≤ q * A + (q + 1) * ε := by
  have haUpper : a ≤ A + ε := by
    have := (abs_le.mp ha).2
    linarith
  have hBUpper : B ≤ b + ε := by
    have := (abs_le.mp hb).1
    linarith
  calc
    B ≤ b + ε := hBUpper
    _ ≤ q * a + ε := by linarith
    _ ≤ q * (A + ε) + ε := by
      gcongr
    _ = q * A + (q + 1) * ε := by ring

/-- A nonnegative one-time form dominated by a zero norm must vanish on the
same diagonal null vector. -/
theorem diagonal_null_descends
    (A B q : ℝ)
    (hB0 : 0 ≤ B)
    (hq : 0 ≤ q)
    (hdom : B ≤ q * A)
    (hA : A = 0) :
    B = 0 := by
  rw [hA] at hdom
  nlinarith

/-- The positive quadratic form used in the basis-only counterexample. -/
def observedForm (x y : ℚ) : ℚ :=
  (1 / 2 : ℚ) * x ^ 2 + (4 / 5 : ℚ) * x * y + (1 / 2 : ℚ) * y ^ 2

/-- The counterexample form is positive definite. -/
theorem observedForm_nonnegative (x y : ℚ) :
    0 ≤ observedForm x y := by
  have hsum : 0 ≤ (9 / 20 : ℚ) * (x + y) ^ 2 := by positivity
  have hdiff : 0 ≤ (1 / 20 : ℚ) * (x - y) ^ 2 := by positivity
  have hid : observedForm x y =
      (9 / 20 : ℚ) * (x + y) ^ 2 + (1 / 20 : ℚ) * (x - y) ^ 2 := by
    simp [observedForm]
    ring
  rw [hid]
  positivity

/-- Each coordinate generator individually satisfies the apparent factor
`q=1/2`. -/
theorem basis_generators_pass :
    observedForm 1 0 = 1 / 2 ∧ observedForm 0 1 = 1 / 2 := by
  norm_num [observedForm]

/-- The sum of the two generators violates the same one-time quadratic
contraction: `9/5 > (1/2)*2 = 1`. -/
theorem basis_checks_do_not_control_linear_combinations :
    observedForm 1 1 = 9 / 5 ∧
      (1 / 2 : ℚ) * (1 ^ 2 + 1 ^ 2) = 1 ∧
      (1 : ℚ) < observedForm 1 1 := by
  norm_num [observedForm]

/-- Exact determinant of the cutoff-total pair
`u=e₁`, `v=e₁+εe₂`. -/
theorem collapsing_gram_determinant (ε : ℚ) :
    1 * (1 + ε ^ 2) - 1 * 1 = ε ^ 2 := by
  ring

/-- Every nonzero cutoff perturbation has positive Gram determinant. -/
theorem cutoff_pair_total_before_collapse
    (ε : ℚ) (hε : ε ≠ 0) :
    0 < 1 * (1 + ε ^ 2) - 1 * 1 := by
  rw [collapsing_gram_determinant]
  exact sq_pos_of_ne_zero hε

/-- At the limiting value `ε=0`, the same named pair loses rank. -/
theorem limiting_pair_rank_collapses :
    (1 : ℚ) * (1 + 0 ^ 2) - 1 * 1 = 0 := by
  norm_num

/-- Strict cutoff contraction factors can approach one; this exact identity is
the finite algebraic shadow of the lost uniform margin. -/
theorem strict_factor_defect (n : ℚ) :
    1 - (1 - 1 / n) = 1 / n := by
  ring

#print axioms approximate_contraction_transfer
#print axioms diagonal_null_descends
#print axioms observedForm_nonnegative
#print axioms basis_generators_pass
#print axioms basis_checks_do_not_control_linear_combinations
#print axioms collapsing_gram_determinant
#print axioms cutoff_pair_total_before_collapse
#print axioms limiting_pair_rank_collapses
#print axioms strict_factor_defect

end YMCommonCoreGramLimitFinite
end MillenniumBraid
