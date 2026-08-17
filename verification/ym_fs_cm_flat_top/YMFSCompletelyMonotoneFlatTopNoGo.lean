import Mathlib

/-!
# Faizal--Shabir completely-monotone flat-top firewall

Finite real algebra only.

A normalized completely monotone multiplier is convex.  If it stays within
`epsilon` of one at the end of a low-energy plateau and within `epsilon` of
zero at a later stop-band point, convexity forces a fixed positive error floor.

This file formalizes only the secant-slope algebra.  It does **not** formalize
Bernstein's theorem, positive measures, spectral functional calculus,
reflection positivity, Yang--Mills, or any Clay theorem.
-/

namespace YMFSCompletelyMonotoneFlatTopNoGo

/-- Cross-multiplied convex-secant estimate.  Here `fa` and `fb` stand for
values of a convex function at `a` and `b`, while the normalized value at zero
is exactly one. -/
theorem flatTop_cross_multiplied
    (a b epsilon fa fb : ℝ)
    (ha : 0 < a)
    (hab : a < b)
    (hfa : 1 - epsilon ≤ fa)
    (hfb : fb ≤ epsilon)
    (hsecant : (b - a) * (fa - 1) ≤ a * (fb - fa)) :
    a ≤ epsilon * (a + b) := by
  have hb0 : 0 ≤ b := le_of_lt (lt_trans ha hab)
  have ha0 : 0 ≤ a := le_of_lt ha
  have hfaMul : b * (1 - epsilon) ≤ b * fa :=
    mul_le_mul_of_nonneg_left hfa hb0
  have hfbMul : a * fb ≤ a * epsilon :=
    mul_le_mul_of_nonneg_left hfb ha0
  nlinarith

/-- Quantitative flat-top approximation barrier:
`epsilon >= a / (a+b)`. -/
theorem flatTop_error_lower_bound
    (a b epsilon fa fb : ℝ)
    (ha : 0 < a)
    (hab : a < b)
    (hfa : 1 - epsilon ≤ fa)
    (hfb : fb ≤ epsilon)
    (hsecant : (b - a) * (fa - 1) ≤ a * (fb - fa)) :
    a / (a + b) ≤ epsilon := by
  have habSum : 0 < a + b := by
    have hb : 0 < b := lt_trans ha hab
    linarith
  apply (div_le_iff₀ habSum).2
  exact flatTop_cross_multiplied a b epsilon fa fb ha hab hfa hfb hsecant

/-- At the source's displayed low/high points `a=1`, `b=4`, every normalized
convex profile has uniform endpoint error at least `1/5`. -/
theorem one_four_error_floor
    (epsilon f1 f4 : ℝ)
    (hf1 : 1 - epsilon ≤ f1)
    (hf4 : f4 ≤ epsilon)
    (hsecant : 3 * (f1 - 1) ≤ f4 - f1) :
    (1 : ℝ) / 5 ≤ epsilon := by
  have hsecant' :
      ((4 : ℝ) - 1) * (f1 - 1) ≤ (1 : ℝ) * (f4 - f1) := by
    norm_num
    exact hsecant
  have h := flatTop_error_lower_bound
    (1 : ℝ) 4 epsilon f1 f4 (by norm_num) (by norm_num)
      hf1 hf4 hsecant'
  norm_num at h ⊢
  exact h

/-- Consequently no profile satisfying the same convex endpoint constraints
can have error strictly below `1/5`. -/
theorem no_one_four_error_below_one_fifth
    (epsilon f1 f4 : ℝ)
    (hepsilon : epsilon < (1 : ℝ) / 5)
    (hf1 : 1 - epsilon ≤ f1)
    (hf4 : f4 ≤ epsilon)
    (hsecant : 3 * (f1 - 1) ≤ f4 - f1) :
    False := by
  have hfloor := one_four_error_floor epsilon f1 f4 hf1 hf4 hsecant
  linarith

#print axioms flatTop_cross_multiplied
#print axioms flatTop_error_lower_bound
#print axioms one_four_error_floor
#print axioms no_one_four_error_below_one_fifth

end YMFSCompletelyMonotoneFlatTopNoGo
