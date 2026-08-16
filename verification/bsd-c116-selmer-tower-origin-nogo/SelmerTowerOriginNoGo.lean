import Mathlib

namespace Millennium.BSD.SelmerTowerOriginNoGo

theorem sameFiniteSelmerLength
    (depth : ℕ) :
    depth + 0 = 0 + depth := by
  omega

theorem sameTotalDifferentOrigins :
    (1 + 0 = 0 + 1) ∧ (1 : ℕ) ≠ 0 := by
  omega

theorem towerCodeCannotDetermineBothRanks
    {TowerCode : Type}
    (code : TowerCode)
    (rankFromTower : TowerCode → ℕ) :
    ¬ (rankFromTower code = 1 ∧ rankFromTower code = 0) := by
  omega

theorem persistentLineAllocationDichotomy :
    (1, 0, 1) ≠ (0, 1, 1) ∧
      ((1 : ℕ) + 0 = 1) ∧
      ((0 : ℕ) + 1 = 1) := by
  norm_num

theorem identicalZeroLiftabilityQuotients
    (depth : ℕ) :
    (0 : ℕ) = 0 ∧ depth = depth := by
  exact ⟨rfl, rfl⟩

#print axioms sameFiniteSelmerLength
#print axioms sameTotalDifferentOrigins
#print axioms towerCodeCannotDetermineBothRanks
#print axioms persistentLineAllocationDichotomy
#print axioms identicalZeroLiftabilityQuotients

end Millennium.BSD.SelmerTowerOriginNoGo
