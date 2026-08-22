import Mathlib

namespace RHMobiusHyperbolaLedger

theorem integerKernel {n : ℝ} (hn : n ≠ 0) :
    n - n * (n + 1) / n
        + n * (n + 1) * (2 * n + 1) / (6 * n ^ 2) =
      n / 3 - 1 / 2 + 1 / (6 * n) := by
  field_simp [hn]
  ring

theorem oneTerm_fourLedger (a d beta x : ℝ) :
    a * (x / (3 * d) - 1 / 2 + d / (6 * x)
      - d ^ 2 * beta / (3 * x ^ 2)) =
      x / 3 * (a / d) - 1 / 2 * a
        + 1 / (6 * x) * (d * a)
        - 1 / (3 * x ^ 2) * (d ^ 2 * a * beta) := by
  ring

theorem centered_background_nonzero
    {c gamma b : ℝ}
    (hc : c = 0)
    (hb : b = c + 2 * gamma)
    (hgamma : gamma ≠ 0) :
    b ≠ 0 := by
  intro hzero
  apply hgamma
  rw [hb, hc] at hzero
  linarith

#print axioms integerKernel
#print axioms oneTerm_fourLedger
#print axioms centered_background_nonzero

end RHMobiusHyperbolaLedger
