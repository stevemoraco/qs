import Mathlib

namespace SixLaneAudit.BoundedCutoffCriterion

/-- A common tail cutoff exists exactly when one can choose valid row cutoffs
that are uniformly bounded. -/
theorem common_cutoff_iff_bounded_row_cutoffs (P : ℕ → ℕ → Prop) :
    (∃ B : ℕ, ∀ k n : ℕ, B ≤ n → P k n) ↔
      ∃ N : ℕ → ℕ, ∃ B : ℕ,
        (∀ k, N k ≤ B) ∧ (∀ k n, N k ≤ n → P k n) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨fun _ => B, B, ?_, ?_⟩
    · intro k
      exact le_rfl
    · intro k n hBn
      exact hB k n hBn
  · rintro ⟨N, B, hbound, htail⟩
    refine ⟨B, ?_⟩
    intro k n hBn
    exact htail k n (le_trans (hbound k) hBn)

#print axioms common_cutoff_iff_bounded_row_cutoffs

end SixLaneAudit.BoundedCutoffCriterion
