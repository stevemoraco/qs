import Mathlib

namespace Millennium.YangMills.FaizalShabirFirstCumulantColorCancellation

theorem odd_two_point_average_zero
    (f x : ℝ)
    (hodd : f (-x) = -f x) :
    (f x + f (-x)) / 2 = 0 := by
  rw [hodd]
  ring

theorem antisymmetric_symmetric_pair_cancels
    (fij fji cij cji : ℝ)
    (hf : fji = -fij)
    (hc : cji = cij) :
    fij * cij + fji * cji = 0 := by
  rw [hf, hc]
  ring

theorem antisymmetric_diagonal_zero
    (fii : ℝ)
    (h : fii = -fii) :
    fii = 0 := by
  linarith

#print axioms odd_two_point_average_zero
#print axioms antisymmetric_symmetric_pair_cancels
#print axioms antisymmetric_diagonal_zero

end Millennium.YangMills.FaizalShabirFirstCumulantColorCancellation
