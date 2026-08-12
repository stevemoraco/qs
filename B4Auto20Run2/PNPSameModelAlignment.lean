import Mathlib
namespace B4Auto20Run2

theorem pnp_same_model_eventual_cofinal_contradiction
    {M : Type} (m : M) (Upper Lower : M → Nat → Prop)
    (hUpper : ∃ N, ∀ n ≥ N, Upper m n)
    (hLower : ∀ N, ∃ n ≥ N, Lower m n)
    (hincompat : ∀ n, ¬ (Upper m n ∧ Lower m n)) :
    False := by
  rcases hUpper with ⟨N, hN⟩
  rcases hLower N with ⟨n, hn, hLn⟩
  exact hincompat n ⟨hN n hn, hLn⟩

theorem pnp_different_models_can_carry_separate_asymptotic_witnesses :
    ∃ mUpper mLower : Bool,
      mUpper ≠ mLower ∧
      (∃ N : Nat, ∀ n ≥ N, mUpper = false) ∧
      (∀ N : Nat, ∃ n ≥ N, mLower = true) := by
  refine ⟨false, true, by decide, ?_, ?_⟩
  · exact ⟨0, by intro n hn; rfl⟩
  · intro N
    exact ⟨N, le_rfl, rfl⟩

#print axioms pnp_same_model_eventual_cofinal_contradiction
#print axioms pnp_different_models_can_carry_separate_asymptotic_witnesses
end B4Auto20Run2
