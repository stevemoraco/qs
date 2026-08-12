import Mathlib

namespace B4Auto20Run3

/-- BANKER: scalar core of the discriminant/index saturation certificate. If a
nondegenerate ambient discriminant is multiplied by the square of a
nonnegative index, equality of ambient and sublattice discriminants forces
index one. The lattice/discriminant identity itself is an external hypothesis. -/
theorem hodge_equal_discriminant_forces_unit_index
    (discL discA idx : ℝ)
    (hdiscL : 0 < discL)
    (hidx : 0 ≤ idx)
    (hchange : discA = idx ^ 2 * discL)
    (hequal : discA = discL) :
    idx = 1 := by
  have hne : discL ≠ 0 := ne_of_gt hdiscL
  have hprod : (idx ^ 2 - 1) * discL = 0 := by
    nlinarith [hchange, hequal]
  have hfactor : idx ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hne
  have hsquare : idx ^ 2 = 1 := by linarith
  nlinarith

/-- CLEANER: the same certificate can be stated as an impossibility of a
strictly larger nonnegative index when the discriminants agree and the ambient
pairing is nondegenerate. -/
theorem hodge_equal_discriminant_excludes_larger_index
    (discL discA idx : ℝ)
    (hdiscL : 0 < discL)
    (hidx : 1 < idx)
    (hchange : discA = idx ^ 2 * discL) :
    discA ≠ discL := by
  intro hequal
  have hunit := hodge_equal_discriminant_forces_unit_index discL discA idx hdiscL
    (le_trans (by norm_num) (le_of_lt hidx)) hchange hequal
  linarith

/-- CRITIC: if the ambient discriminant is zero, discriminant equality carries
no index information at all. Nondegeneracy is therefore load-bearing. -/
theorem hodge_zero_discriminant_hides_index_defect :
    (0 : ℝ) = (2 : ℝ) ^ 2 * 0 ∧
    (0 : ℝ) = 0 ∧
    (2 : ℝ) ≠ 1 := by
  norm_num

#print axioms B4Auto20Run3.hodge_equal_discriminant_forces_unit_index
#print axioms B4Auto20Run3.hodge_equal_discriminant_excludes_larger_index
#print axioms B4Auto20Run3.hodge_zero_discriminant_hides_index_defect

end B4Auto20Run3
