import Mathlib

/-!
# Finite countermodels to two uniform-gap inferences

These are elementary scalar shadows of two load-bearing steps in the audited
2026 Yang–Mills argument. They do not address the Yang–Mills conjecture itself.
-/

namespace Millennium
namespace YMUniformGapCountermodels

/-- A positive initial gap plus a finite nonnegative defect does not imply a
positive residual gap: the defect may consume the entire initial gap. -/
theorem summable_is_not_smaller_than_initial_gap :
    let Δ₀ : ℝ := 1
    let ε₀ : ℝ := 1
    0 < Δ₀ ∧ 0 ≤ ε₀ ∧ Δ₀ - ε₀ = 0 := by
  norm_num

/-- Increasing the excited transfer eigenvalue decreases the spectral gap.
Thus a lower bound on the transfer operator has the wrong direction for
obtaining a positive lower bound on the gap. -/
theorem lower_transfer_bound_can_shrink_gap :
    let λ : ℝ := 1 / 2
    let λ' : ℝ := 3 / 4
    λ ≤ λ' ∧ (1 - λ') < (1 - λ) := by
  norm_num

end YMUniformGapCountermodels
end Millennium
