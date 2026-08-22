import Mathlib

/-!
# Yang--Mills two-loop normal-form finite algebra

This file checks only the coefficient cancellation behind the discrete
transmutation normal form.  It does not construct Yang--Mills theory or prove a mass gap.
-/

namespace Millennium
namespace YMTwoLoopNormalForm

/-- The logarithmic counterterm coefficient which cancels the `g^2` drift. -/
def A (β κ : ℝ) : ℝ := κ / β^2 + 3 / 2

/-- The reciprocal-coordinate `g^2` coefficient is exactly canceled by
`A * (log g)'s` leading coefficient `-β g^2`. -/
theorem drift_coefficient_cancels
    (β κ : ℝ) (hβ : β ≠ 0) :
    κ / β + 3 * β / 2 - A β κ * β = 0 := by
  field_simp [A, hβ]
  ring

/-- Equivalent solved form: the unique scalar counterterm coefficient at this
formal order is `κ/β^2 + 3/2`. -/
theorem solve_counterterm
    (β κ C : ℝ) (hβ : β ≠ 0)
    (h : κ / β + 3 * β / 2 - C * β = 0) :
    C = A β κ := by
  dsimp [A]
  field_simp [hβ] at h ⊢
  nlinarith

end YMTwoLoopNormalForm
end Millennium
