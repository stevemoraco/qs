import Mathlib

/-!
# Finite scalar core of the Yang--Mills weak-coupling trajectory audit

If all tuned Wilson couplings remain in one fixed bounded neighborhood of a
finite center, that sequence cannot be unbounded above and hence cannot realize
`β → +∞`.  This is the elementary core behind the regulator-trajectory gap.

No gauge theory is encoded here.
-/

namespace YangMillsBraid

/-- A fixed absolute-value neighborhood gives a uniform upper bound. -/
theorem fixed_neighborhood_upper_bound
    (β : ℕ → ℝ) (βstar D : ℝ)
    (h : ∀ k : ℕ, |β k - βstar| ≤ D) :
    ∀ k : ℕ, β k ≤ βstar + D := by
  intro k
  have hk : β k - βstar ≤ D := le_trans (le_abs_self (β k - βstar)) (h k)
  linarith

/-- Therefore a sequence trapped in a fixed neighborhood cannot be unbounded above. -/
theorem fixed_neighborhood_not_unbounded_above
    (β : ℕ → ℝ) (βstar D : ℝ)
    (h : ∀ k : ℕ, |β k - βstar| ≤ D) :
    ¬ (∀ B : ℝ, ∃ k : ℕ, B < β k) := by
  intro hunbounded
  rcases hunbounded (βstar + D) with ⟨k, hk⟩
  have hupper := fixed_neighborhood_upper_bound β βstar D h k
  linarith

end YangMillsBraid
