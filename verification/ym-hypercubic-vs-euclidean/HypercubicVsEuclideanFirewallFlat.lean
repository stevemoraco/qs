import Mathlib

namespace Millennium.YangMills

def quarticAnisotropy (x : ℝ × ℝ) : ℝ := x.1^4 + x.2^4

def quarterTurn2 (x : ℝ × ℝ) : ℝ × ℝ := (-x.2, x.1)

noncomputable def rationalRotation2 (x : ℝ × ℝ) : ℝ × ℝ :=
  ((3 / 5 : ℝ) * x.1 - (4 / 5 : ℝ) * x.2,
   (4 / 5 : ℝ) * x.1 + (3 / 5 : ℝ) * x.2)

theorem quartic_anisotropy_quarter_turn_invariant (x : ℝ × ℝ) :
    quarticAnisotropy (quarterTurn2 x) = quarticAnisotropy x := by
  simp [quarticAnisotropy, quarterTurn2]
  ring

theorem rational_rotation_preserves_norm_sq (x : ℝ × ℝ) :
    (rationalRotation2 x).1^2 + (rationalRotation2 x).2^2 = x.1^2 + x.2^2 := by
  simp [rationalRotation2]
  ring

theorem quartic_anisotropy_not_full_rotation_invariant :
    quarticAnisotropy (rationalRotation2 (1, 0)) ≠ quarticAnisotropy (1, 0) := by
  norm_num [quarticAnisotropy, rationalRotation2]

theorem quarter_turn_symmetry_does_not_force_full_rotation_symmetry :
    (∀ x : ℝ × ℝ,
      quarticAnisotropy (quarterTurn2 x) = quarticAnisotropy x) ∧
    (∃ x : ℝ × ℝ,
      quarticAnisotropy (rationalRotation2 x) ≠ quarticAnisotropy x) := by
  constructor
  · exact quartic_anisotropy_quarter_turn_invariant
  · exact ⟨(1, 0), quartic_anisotropy_not_full_rotation_invariant⟩

#print axioms quartic_anisotropy_quarter_turn_invariant
#print axioms rational_rotation_preserves_norm_sq
#print axioms quartic_anisotropy_not_full_rotation_invariant
#print axioms quarter_turn_symmetry_does_not_force_full_rotation_symmetry

end Millennium.YangMills
