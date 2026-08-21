import Mathlib

/-!
# BSD C282: Selmer-corank-two logical firewall

Finite arithmetic shell only. This file does NOT formalize Selmer groups,
Tate--Shafarevich groups, Kato's theorem, or BSD.
-/

namespace Millennium.BSD.SelmerCorankTwoFirewall

/-- The finite countermodel to the invalid implication
`r + d = 2 ∧ r ≤ 2 -> r = 2 ∧ d = 0`. -/
theorem corank_two_does_not_force_rank_two :
    ∃ r d : ℕ,
      r + d = 2 ∧
      r ≤ 2 ∧
      ¬ (r = 2 ∧ d = 0) := by
  refine ⟨0, 2, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Even an independent parity premise on Mordell--Weil rank leaves `(0,2)`. -/
theorem even_rank_still_does_not_force_rank_two :
    ∃ r d : ℕ,
      r + d = 2 ∧
      Even r ∧
      ¬ (r = 2 ∧ d = 0) := by
  refine ⟨0, 2, ?_, ?_, ?_⟩
  · omega
  · exact ⟨0, by omega⟩
  · omega

/-- The missing Sha-corank-zero premise is sufficient for rank two. -/
theorem sha_corank_zero_closes_rank_two
    (r d : ℕ)
    (hsum : r + d = 2)
    (hd : d = 0) :
    r = 2 := by
  omega

#print axioms corank_two_does_not_force_rank_two
#print axioms even_rank_still_does_not_force_rank_two
#print axioms sha_corank_zero_closes_rank_two

end Millennium.BSD.SelmerCorankTwoFirewall
