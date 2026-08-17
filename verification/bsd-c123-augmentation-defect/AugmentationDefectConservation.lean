import Mathlib

namespace Millennium.BSD.AugmentationDefectConservation

theorem augmentation_defect_conservation
    (bsdLhs sha tamD tamM m hSel a h0 l c delta : ℤ)
    (hGZ : bsdLhs = tamD + 2 * m)
    (hKey : 2 * m = sha - hSel + 2 * (a - h0))
    (hLZZ : l = 2 * a)
    (hLocal : c - 2 * h0 = tamM)
    (hDefect : delta = l - hSel - c) :
    bsdLhs - (sha + tamD + tamM) = delta := by
  omega

theorem zero_augmentation_defect_closes_valuation
    (bsdLhs sha tamD tamM m hSel a h0 l c : ℤ)
    (hGZ : bsdLhs = tamD + 2 * m)
    (hKey : 2 * m = sha - hSel + 2 * (a - h0))
    (hLZZ : l = 2 * a)
    (hLocal : c - 2 * h0 = tamM)
    (hAug : l = hSel + c) :
    bsdLhs = sha + tamD + tamM := by
  have hCons := augmentation_defect_conservation
    bsdLhs sha tamD tamM m hSel a h0 l c 0
    hGZ hKey hLZZ hLocal (by omega)
  omega

theorem augmentation_upper_sign
    (bsdLhs sha tamD tamM m hSel a h0 l c : ℤ)
    (hGZ : bsdLhs = tamD + 2 * m)
    (hKey : 2 * m = sha - hSel + 2 * (a - h0))
    (hLZZ : l = 2 * a)
    (hLocal : c - 2 * h0 = tamM)
    (hAug : hSel + c ≤ l) :
    sha + tamD + tamM ≤ bsdLhs := by
  have hCons := augmentation_defect_conservation
    bsdLhs sha tamD tamM m hSel a h0 l c (l - hSel - c)
    hGZ hKey hLZZ hLocal rfl
  omega

theorem unit_window_forces_zero_defect
    (delta : ℤ)
    (hlo : -1 < delta)
    (hhi : delta < 1) :
    delta = 0 := by
  omega

#print axioms augmentation_defect_conservation
#print axioms zero_augmentation_defect_closes_valuation
#print axioms augmentation_upper_sign
#print axioms unit_window_forces_zero_defect

end Millennium.BSD.AugmentationDefectConservation
