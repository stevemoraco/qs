import Mathlib

/-!
# Relative mixed-Gram consumer

Finite real-algebra consumer for the repaired Faizal--Shabir mixed-block route.
It formalizes only the scalar inequalities obtained *after* an interacting
relative Gram-row theorem has supplied

  -theta * internal <= mix.

It does not formalize the Yang--Mills transfer operators, Gram matrices,
locality estimates, regulator uniformity, OS reconstruction, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirMixedGramRelativeRow

/-- A lower relative bound on the signed mixed form controls the internal form
by the complete ideal form without asserting positivity of the mixed block. -/
theorem internal_scaled_le_ideal
    (theta internal mix ideal : ℝ)
    (hideal : ideal = internal + mix)
    (hmix : -theta * internal ≤ mix) :
    (1 - theta) * internal ≤ ideal := by
  rw [hideal]
  nlinarith

/-- If the actual coarse Rayleigh value is bounded by the internal value plus
an unsigned collar error, the same relative mixed-row bound gives a scaled
one-sided estimate against the ideal value. -/
theorem actual_scaled_le_ideal_plus_error
    (theta internal mix ideal err actual : ℝ)
    (htheta : theta ≤ 1)
    (hideal : ideal = internal + mix)
    (hmix : -theta * internal ≤ mix)
    (hactual : actual ≤ internal + err) :
    (1 - theta) * actual ≤ ideal + (1 - theta) * err := by
  have hnonneg : 0 ≤ 1 - theta := by linarith
  have hscaledActual := mul_le_mul_of_nonneg_left hactual hnonneg
  have hinternal := internal_scaled_le_ideal theta internal mix ideal hideal hmix
  nlinarith

/-- Exact target-radius consumer.  Once the scaled ideal-plus-error budget is
below the scaled target and `theta < 1`, the actual radius is below target. -/
theorem target_radius_from_relative_mixed_budget
    (theta internal mix ideal err actual target : ℝ)
    (htheta : theta < 1)
    (hideal : ideal = internal + mix)
    (hmix : -theta * internal ≤ mix)
    (hactual : actual ≤ internal + err)
    (hbudget : ideal + (1 - theta) * err ≤ (1 - theta) * target) :
    actual ≤ target := by
  have hscaled := actual_scaled_le_ideal_plus_error
    theta internal mix ideal err actual (le_of_lt htheta) hideal hmix hactual
  have hpos : 0 < 1 - theta := by linarith
  nlinarith

#print axioms internal_scaled_le_ideal
#print axioms actual_scaled_le_ideal_plus_error
#print axioms target_radius_from_relative_mixed_budget

end Millennium.YangMills.FaizalShabirMixedGramRelativeRow
