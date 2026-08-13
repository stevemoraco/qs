import Mathlib

/-!
Lean-ready scalar core for the Yang--Mills weak-coupling polymer audit.

Conditional only on the paper's scalar range `0 ≤ s ≤ 9/2`, this proves that
for `K(β,s)=exp(-(β/3)s)-1` the absolute activity is maximized at `s=9/2`,
with value `1-exp(-3β/2)`.  Thus this particular sup-norm activity is not a
small weak-coupling parameter as β grows.

No Yang--Mills existence or mass-gap theorem is asserted here.
-/

namespace YangMillsPolymerCore

/-- Endpoint dominates every scalar plaquette action value in `[0,9/2]`. -/
theorem activity_abs_le_endpoint
    (β s : ℝ) (hβ : 0 ≤ β) (hs0 : 0 ≤ s) (hsmax : s ≤ 9 / 2) :
    |Real.exp (-(β / 3) * s) - 1| ≤ 1 - Real.exp (-(3 * β / 2)) := by
  have hbs : 0 ≤ β * s := mul_nonneg hβ hs0
  have ha0 : -(β / 3) * s ≤ 0 := by
    nlinarith
  have hm : β * s ≤ β * (9 / 2) :=
    mul_le_mul_of_nonneg_left hsmax hβ
  have hend : -(3 * β / 2) ≤ -(β / 3) * s := by
    nlinarith [hm]
  have hexpLower :
      Real.exp (-(3 * β / 2)) ≤ Real.exp (-(β / 3) * s) :=
    Real.exp_le_exp.mpr hend
  have hexpUpper : Real.exp (-(β / 3) * s) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr ha0
  have hnonpos : Real.exp (-(β / 3) * s) - 1 ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

/-- The endpoint `s=9/2` attains the bound exactly. -/
theorem activity_endpoint_exact (β : ℝ) (hβ : 0 ≤ β) :
    |Real.exp (-(β / 3) * (9 / 2)) - 1| =
      1 - Real.exp (-(3 * β / 2)) := by
  have harg : -(β / 3) * (9 / 2) = -(3 * β / 2) := by
    ring
  rw [harg]
  have harg0 : -(3 * β / 2) ≤ 0 := by
    nlinarith
  have hexpUpper : Real.exp (-(3 * β / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr harg0
  have hnonpos : Real.exp (-(3 * β / 2)) - 1 ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  ring

/--
Finite supremum certificate: every allowed activity is bounded by the endpoint,
and the endpoint is realized by an allowed scalar value.
-/
theorem activity_supremum_certificate (β : ℝ) (hβ : 0 ≤ β) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 9 / 2 →
      |Real.exp (-(β / 3) * s) - 1| ≤ 1 - Real.exp (-(3 * β / 2))) ∧
    |Real.exp (-(β / 3) * (9 / 2)) - 1| =
      1 - Real.exp (-(3 * β / 2)) := by
  constructor
  · intro s hs0 hsmax
    exact activity_abs_le_endpoint β s hβ hs0 hsmax
  · exact activity_endpoint_exact β hβ

end YangMillsPolymerCore
