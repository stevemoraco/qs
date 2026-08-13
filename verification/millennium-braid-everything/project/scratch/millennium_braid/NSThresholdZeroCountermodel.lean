import Mathlib

/-!
# Navier--Stokes typed-ledger threshold/zero finite countermodel

This formalizes only the logical gap `not (τ < x) -> x = 0` at positive
threshold.  It does not prove or disprove Navier--Stokes.
-/

namespace Millennium
namespace NSThresholdZero

/-- Every positive threshold has a strictly positive subthreshold value. -/
theorem exists_positive_subthreshold (τ : ℝ) (hτ : 0 < τ) :
    ∃ x : ℝ, 0 < x ∧ x ≤ τ ∧ x ≠ 0 ∧ ¬ τ < x := by
  refine ⟨τ / 2, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- Consequently, absence of an above-threshold ledger component cannot by
itself imply exact zero. -/
theorem noAbove_does_not_force_zero :
    ∀ τ : ℝ, 0 < τ → ∃ x : ℝ, (¬ τ < x) ∧ x ≠ 0 := by
  intro τ hτ
  rcases exists_positive_subthreshold τ hτ with ⟨x, hxpos, hxle, hxne, hxnot⟩
  exact ⟨x, hxnot, hxne⟩

end NSThresholdZero
end Millennium
