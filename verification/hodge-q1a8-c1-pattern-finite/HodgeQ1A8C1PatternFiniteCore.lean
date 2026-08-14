import Mathlib

namespace HodgeQ1A8C1PatternFiniteCore

/-!
Finite arithmetic shadow of RH `HODGE_Q1A8_C1_FINITE_PATTERN_CLASSIFICATION_2026-08-14.md`.

This file does NOT formalize K3 surfaces, proximity geometry, alpha support,
stationary/moving singularity classification, normalization, algebraic cycles,
or the Hodge conjecture.  Those are explicit human inputs upstream.
-/

/-- If three double-contact fibres exhaust degree 13 and each off-root
stationary-nonnormal multiplicity is 2 or 4, the complete multiplicity list is
(9,2,2), (7,2,4), (7,4,2), or (5,4,4). -/
theorem three_double_complete_list
    (mq m₁ m₂ : ℕ)
    (h₁ : m₁ = 2 ∨ m₁ = 4)
    (h₂ : m₂ = 2 ∨ m₂ = 4)
    (hsum : mq + m₁ + m₂ = 13) :
    (mq = 9 ∧ m₁ = 2 ∧ m₂ = 2) ∨
    (mq = 7 ∧ m₁ = 2 ∧ m₂ = 4) ∨
    (mq = 7 ∧ m₁ = 4 ∧ m₂ = 2) ∨
    (mq = 5 ∧ m₁ = 4 ∧ m₂ = 4) := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> omega

/-- Up to interchanging the two off-root fibres, the q-root multiplicity in
three-double C1 is one of 9,7,5. -/
theorem three_double_qroot_values
    (mq m₁ m₂ : ℕ)
    (h₁ : m₁ = 2 ∨ m₁ = 4)
    (h₂ : m₂ = 2 ∨ m₂ = 4)
    (hsum : mq + m₁ + m₂ = 13) :
    mq = 9 ∨ mq = 7 ∨ mq = 5 := by
  rcases three_double_complete_list mq m₁ m₂ h₁ h₂ hsum with h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

/-- In the two-double + one simple-transverse allocation, an even
stationary-nonnormal q-root with normalization needing at most three rational
exceptionals has the unique finite pattern (mq,mo)=(8,4).

`mq = 2*k` is the finite shadow of the stationary-nonnormal `m=2k` theorem;
`k-1 ≤ 3` is the finite shadow of the three available root exceptionals. -/
theorem stationary_two_double_unique
    (mq mo k : ℕ)
    (hoff : mo = 2 ∨ mo = 4)
    (hsum : mq + mo + 1 = 13)
    (heven : mq = 2 * k)
    (hcapacity : k - 1 ≤ 3) :
    mq = 8 ∧ mo = 4 := by
  rcases hoff with rfl | rfl <;> omega

/-- The competing (10,2,1) arithmetic allocation needs k=5 and therefore
four A-type exceptional curves, exceeding a three-curve root budget. -/
theorem ten_two_one_exceeds_three_curve_budget
    (k : ℕ)
    (hk : 10 = 2 * k) :
    ¬ (k - 1 ≤ 3) := by
  omega

/-- The surviving (8,4,1) allocation has exactly k=4 and hence exactly three
finite A-type exceptional curves. -/
theorem eight_four_one_exact_three_curve_budget :
    ∃ k : ℕ, 8 = 2 * k ∧ k - 1 = 3 := by
  exact ⟨4, by omega, by omega⟩

#print axioms three_double_complete_list
#print axioms three_double_qroot_values
#print axioms stationary_two_double_unique
#print axioms ten_two_one_exceeds_three_curve_budget
#print axioms eight_four_one_exact_three_curve_budget

end HodgeQ1A8C1PatternFiniteCore
