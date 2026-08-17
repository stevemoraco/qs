import Mathlib

namespace Millennium.YangMills.PhysicalMassScalingFirewall

def physicalMass (mLat a : ℚ) : ℚ := mLat / a

theorem physicalMass_geometric
    (mLat a0 b : ℚ) (k : ℕ)
    (ha0 : a0 ≠ 0) (hb : b ≠ 0) :
    physicalMass mLat (a0 * b^k) = physicalMass mLat a0 / b^k := by
  have hpow : b^k ≠ 0 := pow_ne_zero k hb
  simp only [physicalMass]
  field_simp [ha0, hpow]
  ring

theorem quadratic_recurrence_invariant_step
    (C eps x delta next : ℚ)
    (hrec : next ≤ C * x^2 + C * delta)
    (hquad : C * x^2 ≤ eps / 2)
    (hrem : C * delta ≤ eps / 2) :
    next ≤ eps := by
  linarith

theorem additive_one_blocks_small_half_budget
    (C eps r : ℚ)
    (hC : 0 < C)
    (heps : eps < 2 * C)
    (hr : 0 ≤ r) :
    ¬ (C * (r + 1) ≤ eps / 2) := by
  intro h
  nlinarith

theorem finite_window_physical_floor
    (mLat a A : ℚ)
    (hm : 0 ≤ mLat)
    (ha : 0 < a)
    (hA : a ≤ A) :
    mLat / A ≤ mLat / a := by
  exact div_le_div_of_nonneg_left hm ha hA

#print axioms physicalMass_geometric
#print axioms quadratic_recurrence_invariant_step
#print axioms additive_one_blocks_small_half_budget
#print axioms finite_window_physical_floor

end Millennium.YangMills.PhysicalMassScalingFirewall
