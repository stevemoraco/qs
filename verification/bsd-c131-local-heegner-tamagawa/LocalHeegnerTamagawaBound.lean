import Mathlib

namespace Millennium.BSD.LocalHeegnerTamagawaBound

theorem globalIndexAtLeastFloor
    (t globalIndex sLen : ℕ)
    (hStructure : globalIndex = t + sLen) :
    t ≤ globalIndex := by
  omega

theorem localIndexBoundsSha
    (t globalIndex localIndex sLen shaVal : ℕ)
    (hStructure : globalIndex = t + sLen)
    (hLocalization : globalIndex ≤ localIndex)
    (hSha : shaVal = 2 * sLen) :
    shaVal ≤ 2 * (localIndex - t) := by
  omega

theorem localFloorKillsSha
    (t globalIndex localIndex sLen shaVal : ℕ)
    (hStructure : globalIndex = t + sLen)
    (hLocalization : globalIndex ≤ localIndex)
    (hLocalFloor : localIndex = t)
    (hSha : shaVal = 2 * sLen) :
    globalIndex = t ∧ sLen = 0 ∧ shaVal = 0 := by
  omega

theorem strictLocalWindowKillsSha
    (t globalIndex localIndex sLen shaVal : ℕ)
    (hStructure : globalIndex = t + sLen)
    (hLocalization : globalIndex ≤ localIndex)
    (hWindow : localIndex < t + 1)
    (hSha : shaVal = 2 * sLen) :
    globalIndex = t ∧ sLen = 0 ∧ shaVal = 0 := by
  omega

theorem belowFloorIsImpossible
    (t globalIndex localIndex sLen : ℕ)
    (hStructure : globalIndex = t + sLen)
    (hLocalization : globalIndex ≤ localIndex)
    (hBelow : localIndex < t) :
    False := by
  omega

theorem localExcessBoundsSha
    (t globalIndex localIndex sLen shaVal m : ℕ)
    (hStructure : globalIndex = t + sLen)
    (hLocalization : globalIndex ≤ localIndex)
    (hLocalBound : localIndex ≤ t + m)
    (hSha : shaVal = 2 * sLen) :
    shaVal ≤ 2 * m := by
  omega

#print axioms globalIndexAtLeastFloor
#print axioms localIndexBoundsSha
#print axioms localFloorKillsSha
#print axioms strictLocalWindowKillsSha
#print axioms belowFloorIsImpossible
#print axioms localExcessBoundsSha

end Millennium.BSD.LocalHeegnerTamagawaBound
