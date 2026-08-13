import Mathlib

namespace MillenniumRun14

/-- Nonnegativity of a physical gap does not justify replacing
`exp (a * Δ)` by `exp a`.  This is the finite scalar error in the
absolute-defect gap bootstrap: at any positive scale, Δ = 2 is a counterexample. -/
theorem ym_nonnegative_gap_does_not_bound_exp_factor
    (a : ℝ) (ha : 0 < a) :
    ¬ (∀ Δ : ℝ, 0 ≤ Δ → Real.exp (a * Δ) ≤ Real.exp a) := by
  intro h
  have hbad := h 2 (by norm_num)
  have harg : a < a * 2 := by nlinarith
  have hexp : Real.exp a < Real.exp (a * 2) := Real.exp_lt_exp.mpr harg
  exact (not_lt_of_ge hbad) hexp

end MillenniumRun14
