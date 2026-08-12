import Mathlib

/-!
# Weak-L3 logarithmic-budget scalar firewall

This file formalizes only the scalar logarithm-to-exponential rearrangement
used after the analytic Lorentz distribution estimate. It does not formalize
Lorentz spaces, the Barker–Prange theorem, the Navier–Stokes equation, or the
Clay target.
-/

namespace NSWeakL3LogEnstrophy

/-- BANKER → CLEANER: a logarithmic upper budget gives the exact exponential
lower bound on the dimensionless ratio. -/
theorem log_budget_forces_exponential_ratio
    (s a x : ℝ)
    (ha : 0 < a)
    (hx : 0 < x)
    (hbudget : s ≤ 3 * a + 3 * a * Real.log x) :
    Real.exp (s / (3 * a) - 1) ≤ x := by
  have h3a : 0 < 3 * a := by positivity
  have hdiv : s / (3 * a) ≤ 1 + Real.log x := by
    apply (div_le_iff₀ h3a).2
    nlinarith [hbudget]
  have hexponent : s / (3 * a) - 1 ≤ Real.log x := by
    linarith
  calc
    Real.exp (s / (3 * a) - 1)
        ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hexponent
    _ = x := Real.exp_log hx

/-- The exact dimensional form used in the weak-L3 application. Here `A` is
the distribution-cap scale, `E` the kinetic energy, `F` the squared L6 norm,
and `S` the cubic mass. The analytic layer-cake theorem supplies `hbudget`;
this declaration verifies only its load-bearing scalar rearrangement. -/
theorem dimensional_exponential_lower_bound
    (A E F S : ℝ)
    (hA : 0 < A)
    (hE : 0 < E)
    (hF : 0 < F)
    (hbudget :
      S ≤ 3 * A ^ 3 +
        3 * A ^ 3 * Real.log ((F * E) / A ^ 4)) :
    (A ^ 4 / E) * Real.exp (S / (3 * A ^ 3) - 1) ≤ F := by
  have hA3 : 0 < A ^ 3 := pow_pos hA 3
  have hA4 : 0 < A ^ 4 := pow_pos hA 4
  have hx : 0 < (F * E) / A ^ 4 := by positivity
  have hexp := log_budget_forces_exponential_ratio
    S (A ^ 3) ((F * E) / A ^ 4) hA3 hx hbudget
  have hscale : 0 ≤ A ^ 4 / E := le_of_lt (div_pos hA4 hE)
  have hmul := mul_le_mul_of_nonneg_left hexp hscale
  calc
    (A ^ 4 / E) * Real.exp (S / (3 * A ^ 3) - 1)
        ≤ (A ^ 4 / E) * ((F * E) / A ^ 4) := hmul
    _ = F := by
      field_simp [ne_of_gt hA, ne_of_gt hE]

/-- CRITIC: a power model with exponent below one still has a finite
antiderivative budget. Positivity of the exponent is not needed for this upper
bound; only `gamma < 1` and nonnegative cutoff are load-bearing. -/
theorem subunit_power_antiderivative_budget
    (gamma epsilon : ℝ)
    (hgamma1 : gamma < 1)
    (hepsilon : 0 ≤ epsilon) :
    (1 - epsilon ^ (1 - gamma)) / (1 - gamma)
      ≤ 1 / (1 - gamma) := by
  have hden : 0 < 1 - gamma := by linarith
  have hpow : 0 ≤ epsilon ^ (1 - gamma) := Real.rpow_nonneg hepsilon _
  apply (div_le_div_iff_of_pos_right hden).2
  linarith

#print axioms log_budget_forces_exponential_ratio
#print axioms dimensional_exponential_lower_bound
#print axioms subunit_power_antiderivative_budget

end NSWeakL3LogEnstrophy
