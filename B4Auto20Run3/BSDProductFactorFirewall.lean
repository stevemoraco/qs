import Mathlib

namespace B4Auto20Run3

theorem bsd_positive_prefactor_exactifies_defect
    (w d : ℝ) (hw : 0 < w) (hprod : w * d = 0) :
    d = 0 := by
  rcases mul_eq_zero.mp hprod with hw0 | hd0
  · exact False.elim ((ne_of_gt hw) hw0)
  · exact hd0

theorem bsd_zero_prefactor_hides_nonzero_defect :
    ∃ w d : ℝ, 0 ≤ w ∧ 0 ≤ d ∧ w * d = 0 ∧ d ≠ 0 := by
  exact ⟨0, 1, by norm_num⟩

#print axioms B4Auto20Run3.bsd_positive_prefactor_exactifies_defect
#print axioms B4Auto20Run3.bsd_zero_prefactor_hides_nonzero_defect

end B4Auto20Run3
