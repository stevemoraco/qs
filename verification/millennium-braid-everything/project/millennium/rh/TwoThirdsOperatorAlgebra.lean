import Mathlib

/-!
# Scalar firewall for the two-thirds feature-operator route

This file formalizes two load-bearing algebraic identities used in the proposed
rank--trace--inertia argument.  It does **not** formalize the spectral theorem,
von Neumann's trace inequality, the zeta pair-correlation input, or RH.
-/

namespace Millennium.RH.TwoThirdsOperator

/-- The paired positive/negative eigenvalue summand is a manifest square plus
    a nonnegative remainder. -/
theorem paired_summand_identity (p b : ℝ) :
    (p - 1) ^ 2 + b ^ 2 + 4 * b - 2 * p * b =
      (p - b - 1) ^ 2 + 2 * b := by
  ring

/-- Consequently the paired summand is nonnegative when the negative-part
    eigenvalue `b` is nonnegative. -/
theorem paired_summand_nonneg (p b : ℝ) (hb : 0 ≤ b) :
    0 ≤ (p - 1) ^ 2 + b ^ 2 + 4 * b - 2 * p * b := by
  rw [paired_summand_identity]
  positivity

/-- Final arithmetic ledger: the abstract rank bound plus the count and moment
    budgets force a two-thirds lower bound. -/
theorem two_thirds_ledger
    (N s r M p eps : ℝ)
    (hrank : s ≥ r)
    (hrt : r ≥ 2 * M + 4 * (N - M) - 4 * p - (4 / 3 + eps) * N)
    (hcount : M + 2 * p ≤ N) :
    s ≥ (2 / 3 - eps) * N := by
  linarith

/-- The exact zero-error specialization. -/
theorem two_thirds_ledger_exact
    (N s r M p : ℝ)
    (hrank : s ≥ r)
    (hrt : r ≥ 2 * M + 4 * (N - M) - 4 * p - (4 / 3) * N)
    (hcount : M + 2 * p ≤ N) :
    s ≥ (2 / 3) * N := by
  linarith

end Millennium.RH.TwoThirdsOperator
