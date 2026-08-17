import Mathlib

namespace Millennium.YangMills.FaizalShabirHypercubicO4Firewall

def hypercubicQuartic (x y : ℝ) : ℝ := x ^ 4 + y ^ 4

theorem hypercubicQuartic_neg_left (x y : ℝ) :
    hypercubicQuartic (-x) y = hypercubicQuartic x y := by
  unfold hypercubicQuartic
  ring

theorem hypercubicQuartic_neg_right (x y : ℝ) :
    hypercubicQuartic x (-y) = hypercubicQuartic x y := by
  unfold hypercubicQuartic
  ring

theorem hypercubicQuartic_swap (x y : ℝ) :
    hypercubicQuartic y x = hypercubicQuartic x y := by
  simp [hypercubicQuartic, add_comm]

theorem pythagorean_same_radius :
    ((1 : ℝ) ^ 2 + 0 ^ 2) =
      ((3 / 5 : ℝ) ^ 2 + (4 / 5 : ℝ) ^ 2) := by
  norm_num

theorem hypercubicQuartic_not_radial_witness :
    hypercubicQuartic 1 0 ≠ hypercubicQuartic (3 / 5) (4 / 5) := by
  norm_num [hypercubicQuartic]

theorem rational_rotation_sends_axis :
    ((3 / 5 : ℝ) * 1 - (4 / 5 : ℝ) * 0,
      (4 / 5 : ℝ) * 1 + (3 / 5 : ℝ) * 0) =
      ((3 / 5 : ℝ), (4 / 5 : ℝ)) := by
  norm_num

theorem hypercubic_invariance_does_not_force_rotation_invariance :
    hypercubicQuartic 1 0 ≠
      hypercubicQuartic
        ((3 / 5 : ℝ) * 1 - (4 / 5 : ℝ) * 0)
        ((4 / 5 : ℝ) * 1 + (3 / 5 : ℝ) * 0) := by
  norm_num [hypercubicQuartic]

#print axioms hypercubicQuartic_neg_left
#print axioms hypercubicQuartic_neg_right
#print axioms hypercubicQuartic_swap
#print axioms pythagorean_same_radius
#print axioms hypercubicQuartic_not_radial_witness
#print axioms rational_rotation_sends_axis
#print axioms hypercubic_invariance_does_not_force_rotation_invariance

end Millennium.YangMills.FaizalShabirHypercubicO4Firewall
