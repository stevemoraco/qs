import Mathlib

namespace Millennium.BSD.DengLiChebotarevDensity

theorem primeDensity : (2 : ℚ) / 12 = 1 / 6 := by
  norm_num

theorem orderedPairDensity : ((1 : ℚ) / 6) ^ 2 = 1 / 36 := by
  norm_num

theorem unorderedPairDensity : ((1 : ℚ) / 36) / 2 = 1 / 72 := by
  norm_num

theorem orderedStateCount : (2 : ℕ) * 2 = 4 ∧ (12 : ℕ) * 12 = 144 := by
  norm_num

theorem orderedStateFraction : (4 : ℚ) / 144 = 1 / 36 := by
  norm_num

#print axioms primeDensity
#print axioms orderedPairDensity
#print axioms unorderedPairDensity
#print axioms orderedStateCount
#print axioms orderedStateFraction

end Millennium.BSD.DengLiChebotarevDensity
