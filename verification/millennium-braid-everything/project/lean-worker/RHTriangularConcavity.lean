import Mathlib

namespace RHTriangularConcavity

/-- Algebraic core of the RH triangular-concavity forward implication:
a negative linear drift dominates any uniformly bounded perturbation once the
linear magnitude exceeds the bound. This theorem contains no zeta input. -/
theorem negative_linear_drift_dominates
    {h a err M : ℝ}
    (hh : h < 0)
    (hM : 0 ≤ M)
    (herr : |err| ≤ M)
    (hdom : M < (-6 * h) * a) :
    6 * h * a + err < 0 := by
  have herr_le : err ≤ M := le_trans (le_abs_self err) herr
  nlinarith

/-- A slightly more abstract version, useful for any positive drift magnitude. -/
theorem negative_drift_dominates
    {c a err M : ℝ}
    (hc : 0 < c)
    (hM : 0 ≤ M)
    (herr : |err| ≤ M)
    (hdom : M < c * a) :
    -c * a + err < 0 := by
  have herr_le : err ≤ M := le_trans (le_abs_self err) herr
  nlinarith

/-- The explicit limiting constant used in the human note is negative once
one supplies the elementary numerical inequality `4 < γ + π/2 + log(8π)`.
The analytic identification of Euler's constant/digamma is deliberately not
smuggled into this algebraic firewall. -/
theorem six_times_negative {h : ℝ} (hh : h < 0) : 6 * h < 0 := by
  positivity

#print axioms negative_linear_drift_dominates
#print axioms negative_drift_dominates
#print axioms six_times_negative

end RHTriangularConcavity
