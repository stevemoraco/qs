import Mathlib

namespace B4.Run21.BSD

theorem banker_zero_remainder_total {q r total : ℕ}
    (hdecomp : total = q + r) (hr : r = 0) :
    total = q := by
  omega

theorem critic_fixed_quotient_can_hide_remainder :
    ∃ q r total : ℕ,
      q = 1 ∧ r = 1 ∧ total = q + r ∧ total ≠ q := by
  exact ⟨1, 1, 2, rfl, rfl, rfl, by decide⟩

theorem cleaner_total_eq_quotient_iff_remainder_zero {q r total : ℕ}
    (hdecomp : total = q + r) :
    total = q ↔ r = 0 := by
  omega

#print axioms banker_zero_remainder_total
#print axioms critic_fixed_quotient_can_hide_remainder
#print axioms cleaner_total_eq_quotient_iff_remainder_zero

end B4.Run21.BSD
