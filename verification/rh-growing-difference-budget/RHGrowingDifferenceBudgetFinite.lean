import Mathlib

/-!
# RH growing finite-difference detector/suppression firewall — finite core

HONESTY BOUNDARY

This file formalizes only:

* the exact multiplier of an iterated frozen-step forward difference on one
  complex exponential;
* scalar inequalities comparing a mode depth with an attenuation budget.

It does NOT formalize the Riemann zeta function, its zeros, the explicit
formula, prime-counting functions, pseudoprimes, asymptotic limits, or RH.

No `sorry`, `admit`, custom axiom, or result-equivalent placeholder is intended.
A clean compiler receipt is required before calling this source Lean-verified.
-/

namespace Millennium
namespace RH
namespace GrowingDifferenceBudget

/-- Iterated forward difference with one frozen complex step. -/
def forwardDiff (s : ℂ) : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f, z => f z
  | m + 1, f, z => forwardDiff s m f (z + s) - forwardDiff s m f z

/-- Exact finite-difference multiplier on a complex exponential. -/
theorem forwardDiff_exp (s lam z : ℂ) (m : ℕ) :
    forwardDiff s m (fun w => Complex.exp (lam * w)) z =
      Complex.exp (lam * z) * (Complex.exp (lam * s) - 1) ^ m := by
  induction m generalizing z with
  | zero => simp [forwardDiff]
  | succ m ih =>
      simp only [forwardDiff]
      rw [ih (z + s), ih z]
      rw [mul_add, Complex.exp_add, pow_succ]
      ring

/-- A mode is no longer exponentially visible once its total depth budget is
at most the attenuation budget. -/
theorem attenuation_kills_mode
    {depth T budget : ℝ}
    (h : depth * T ≤ budget) :
    depth * T - budget ≤ 0 := by
  linarith

/-- A mode remains positively visible when its depth budget strictly exceeds
the attenuation budget. -/
theorem mode_visible_beyond_budget
    {depth T budget : ℝ}
    (h : budget < depth * T) :
    0 < depth * T - budget := by
  linarith

/-- A half-exponent attenuation budget kills every depth at most one half. -/
theorem half_envelope_budget_kills_nontrivial_depth
    {depth T budget : ℝ}
    (hdepth : depth ≤ (1 : ℝ) / 2)
    (hT : 0 ≤ T)
    (hbudget : T / 2 ≤ budget) :
    depth * T - budget ≤ 0 := by
  have hmode : depth * T ≤ T / 2 := by
    have := mul_le_mul_of_nonneg_right hdepth hT
    nlinarith
  linarith

/-- More generally, suppressing an envelope of exponent `envelope` also hides
all modes no deeper than that envelope. -/
theorem envelope_budget_hides_shallower_mode
    {depth envelope T budget : ℝ}
    (hdepth : depth ≤ envelope)
    (hT : 0 ≤ T)
    (hbudget : envelope * T ≤ budget) :
    depth * T - budget ≤ 0 := by
  have hmode : depth * T ≤ envelope * T :=
    mul_le_mul_of_nonneg_right hdepth hT
  linarith

/-- If the attenuation budget is sublinear relative to every fixed positive
mode depth, the finite scalar endpoint remains positive. -/
theorem subdepth_budget_preserves_mode
    {depth T budget : ℝ}
    (hdepth : 0 < depth)
    (hT : 0 < T)
    (hbudget : budget < depth * T) :
    0 < depth * T - budget := by
  linarith

#print axioms Millennium.RH.GrowingDifferenceBudget.forwardDiff_exp
#print axioms Millennium.RH.GrowingDifferenceBudget.attenuation_kills_mode
#print axioms Millennium.RH.GrowingDifferenceBudget.mode_visible_beyond_budget
#print axioms Millennium.RH.GrowingDifferenceBudget.half_envelope_budget_kills_nontrivial_depth
#print axioms Millennium.RH.GrowingDifferenceBudget.envelope_budget_hides_shallower_mode
#print axioms Millennium.RH.GrowingDifferenceBudget.subdepth_budget_preserves_mode

end GrowingDifferenceBudget
end RH
end Millennium
