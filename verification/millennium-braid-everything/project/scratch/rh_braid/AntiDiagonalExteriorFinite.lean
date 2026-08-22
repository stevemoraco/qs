import Mathlib

/-!
# Finite algebra for the anti-diagonal exterior RH reduction

This file records only reusable scalar algebra/sign lemmas behind the
anti-diagonal identity. It does not formalize the analytic zero sum,
Laplace growth theorem, explicit formula, or RH.
-/

namespace RHProof
namespace AntiDiagonalExterior

/-- Algebraic anti-diagonal specialization of the first-jet scalar correlator.
Here `Fc`, `Fpc`, `Fppc` stand for conjugate values. -/
theorem anti_diagonal_algebra
    (F Fp Fpp Fc Fpc Fppc : ℂ) :
    2 * Fp * (-Fpc) - F * Fppc - Fpp * Fc
      = -(2 * Fp * Fpc + F * Fppc + Fpp * Fc) := by
  ring

/-- The reflection-pair quadratic coefficient is strictly negative whenever
multiplicity, depth, and window modulus are nonzero/positive. -/
theorem reflection_pair_strictly_negative
    (m y n : ℝ) (hm : 0 < m) (hy : y ≠ 0) (hn : 0 < n) :
    -4 * m^2 * y^2 * n^4 < 0 := by
  have hym : 0 < y^2 := sq_pos_of_ne_zero hy
  positivity

/-- The fourth-order reflected factor has the wrong sign for a negative detector. -/
theorem reflection_fourth_positive
    (y : ℝ) (hy : y ≠ 0) :
    0 < 16 * y^4 := by
  have hym : 0 < y^2 := sq_pos_of_ne_zero hy
  positivity

/-- The sixth-order reflected factor returns to the negative sign, but only at
sixth order in the horizontal depth. -/
theorem reflection_sixth_negative
    (y : ℝ) (hy : y ≠ 0) :
    -64 * y^6 < 0 := by
  have hym : 0 < y^2 := sq_pos_of_ne_zero hy
  positivity

/-- On a real pair, every even derivative factor is nonnegative at orders two
and four; this is the finite sign core behind RH-side positive definiteness. -/
theorem real_pair_even_factors_nonnegative
    (x y : ℝ) :
    0 <= (x - y)^2 ∧ 0 <= (x - y)^4 := by
  constructor <;> positivity

end AntiDiagonalExterior
end RHProof
