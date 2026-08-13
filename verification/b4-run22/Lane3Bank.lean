import Mathlib

namespace B4.Run22.Lane3

theorem banker_two_terms_zero {a b total : Nat}
    (h : total = a + b) (ha : a = 0) (hb : b = 0) :
    total = 0 := by
  omega

theorem critic_first_term_zero_not_enough :
    ∃ a b total : Nat,
      a = 0 ∧ b = 1 ∧ total = a + b ∧ total ≠ 0 := by
  exact ⟨0, 1, 1, rfl, rfl, rfl, by decide⟩

theorem cleaner_sum_zero_iff_both_terms_zero {a b total : Nat}
    (h : total = a + b) :
    total = 0 ↔ a = 0 ∧ b = 0 := by
  omega

#print axioms banker_two_terms_zero
#print axioms critic_first_term_zero_not_enough
#print axioms cleaner_sum_zero_iff_both_terms_zero

end B4.Run22.Lane3
