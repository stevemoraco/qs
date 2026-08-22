import Mathlib

namespace HodgeQ1A9Double3Deficit

/-- Finite arithmetic shadow of the corrected nonstationary root budget.
If at least one unit resource stays on the root, the moving/transverse root
plus the off-root `2w` budget cannot reach alpha degree 13. -/
theorem nonstationary_root_with_one_unit_le_eleven
    {s m off : ℕ}
    (hs1 : 1 ≤ s)
    (hs6 : s ≤ 6)
    (hm : 2 * m ≤ s + 2)
    (hoff : off ≤ 2 * (6 - s)) :
    m + off ≤ 11 := by
  omega

/-- In the exceptional `s=0`, root-multiplicity-one branch, degree 13 forces
exact saturation of the off-root degree budget. -/
theorem simple_root_forces_offroot_twelve
    {off : ℕ}
    (hdeg : 1 + off = 13) :
    off = 12 := by
  omega

/-- The stationary-nonnormal resource maximum is 16 while the exact alpha
degree is 13, so the total deficit is three. This lemma records the complete
parity-compatible split of that deficit. -/
theorem parity_split_of_three
    {δroot δoff : ℕ}
    (hsum : δroot + δoff = 3)
    (hroot_even : δroot % 2 = 0)
    (hoff_odd : δoff % 2 = 1) :
    (δroot = 0 ∧ δoff = 3) ∨
    (δroot = 2 ∧ δoff = 1) := by
  omega

/-- Conversely, the two surviving deficit rows really have total deficit
three and the required parity. -/
theorem deficit_rows_are_valid
    {δroot δoff : ℕ}
    (hrows : (δroot = 0 ∧ δoff = 3) ∨
             (δroot = 2 ∧ δoff = 1)) :
    δroot + δoff = 3 ∧ δroot % 2 = 0 ∧ δoff % 2 = 1 := by
  rcases hrows with h | h <;> rcases h with ⟨rfl, rfl⟩ <;> norm_num

#print axioms nonstationary_root_with_one_unit_le_eleven
#print axioms simple_root_forces_offroot_twelve
#print axioms parity_split_of_three
#print axioms deficit_rows_are_valid

end HodgeQ1A9Double3Deficit
