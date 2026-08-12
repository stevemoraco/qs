import Mathlib

namespace B4Auto20Run3

theorem pnp_every_exponent_has_larger_threshold :
    ∀ c : ℕ, ∃ n : ℕ, c < n := by
  intro c
  exact ⟨c + 1, Nat.lt_succ_self c⟩

theorem pnp_no_single_threshold_beats_every_exponent :
    ¬ ∃ n : ℕ, ∀ c : ℕ, c < n := by
  rintro ⟨n, hn⟩
  exact (Nat.lt_irrefl n) (hn n)

#print axioms B4Auto20Run3.pnp_every_exponent_has_larger_threshold
#print axioms B4Auto20Run3.pnp_no_single_threshold_beats_every_exponent

end B4Auto20Run3
