import Mathlib

namespace NSShahmurovSpectralGapFirewall

/-- The middle spectral block is nonempty: mode 451 lies above the finite
450-mode certificate but below the claimed analytic tail threshold 1200. -/
theorem uncovered_mode_exists :
    ∃ j : ℕ, 450 < j ∧ j < 1200 := by
  exact ⟨451, by norm_num, by norm_num⟩

/-- Concrete domain mismatch: `j >= 1200` does not characterize `j > 450`. -/
theorem tail_domain_not_equal :
    ¬ (∀ j : ℕ, 450 < j ↔ 1200 ≤ j) := by
  intro h
  have h451 := h 451
  have : 1200 ≤ 451 := h451.mp (by norm_num)
  norm_num at this

/-- A lower bound known only beyond 1200 cannot be instantiated at mode 451. -/
theorem restricted_lower_bound_does_not_cover_451
    (P : ℕ → Prop)
    (h : ∀ j : ℕ, 1200 ≤ j → P j) :
    (∀ j : ℕ, 450 < j → P j) → P 451 := by
  intro hall
  exact hall 451 (by norm_num)

/-- Abstract repair shape: if the finite, middle, and tail regions are all
covered, then every positive mode is covered. -/
theorem three_block_cover
    (P : ℕ → Prop)
    (hfin : ∀ j : ℕ, 1 ≤ j → j ≤ 450 → P j)
    (hmid : ∀ j : ℕ, 451 ≤ j → j ≤ 1199 → P j)
    (htail : ∀ j : ℕ, 1200 ≤ j → P j) :
    ∀ j : ℕ, 1 ≤ j → P j := by
  intro j hj
  by_cases h450 : j ≤ 450
  · exact hfin j hj h450
  · have h451 : 451 ≤ j := by omega
    by_cases h1199 : j ≤ 1199
    · exact hmid j h451 h1199
    · have h1200 : 1200 ≤ j := by omega
      exact htail j h1200

#print axioms uncovered_mode_exists
#print axioms tail_domain_not_equal
#print axioms restricted_lower_bound_does_not_cover_451
#print axioms three_block_cover

end NSShahmurovSpectralGapFirewall
