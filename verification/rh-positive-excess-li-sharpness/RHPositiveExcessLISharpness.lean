import Mathlib

namespace RHPositiveExcessLISharpness

/--
Finite block-accounting core.  A lower bound on occupied mass and a lower
bound on the weight combine monotonically into a lower bound on the weighted
positive contribution.
-/
theorem block_mass_weight_floor
    (h δ U mass wFloor weight : ℝ)
    (hh : 0 ≤ h)
    (hmass : 0 ≤ mass)
    (hwFloor : 0 ≤ wFloor)
    (hm : δ * U ≤ mass)
    (hw : wFloor ≤ weight) :
    h * δ * U * wFloor ≤ h * mass * weight := by
  have h₁ : h * (δ * U) ≤ h * mass :=
    mul_le_mul_of_nonneg_left hm hh
  have h₂ : h * (δ * U) * wFloor ≤ h * mass * wFloor :=
    mul_le_mul_of_nonneg_right h₁ hwFloor
  have h₃ : h * mass * wFloor ≤ h * mass * weight :=
    mul_le_mul_of_nonneg_left hw (mul_nonneg hh hmass)
  exact (by simpa [mul_assoc] using h₂.trans h₃)

/-- At the critical reciprocal block weight, the block scale cancels exactly. -/
theorem critical_weight_cancels
    (h δ U : ℝ)
    (hU : U ≠ 0) :
    (h * δ * U) / (2 * U) = h * δ / 2 := by
  field_simp [hU]

/-- A uniform positive floor on finitely many disjoint blocks accumulates linearly. -/
theorem repeated_floor_accumulates
    {n : ℕ}
    (a : Fin n → ℝ)
    (c : ℝ)
    (hfloor : ∀ i, c ≤ a i) :
    (n : ℝ) * c ≤ ∑ i, a i := by
  calc
    (n : ℝ) * c = ∑ _i : Fin n, c := by simp
    _ ≤ ∑ i, a i := by
      exact Finset.sum_le_sum fun i _hi => hfloor i

#print axioms RHPositiveExcessLISharpness.block_mass_weight_floor
#print axioms RHPositiveExcessLISharpness.critical_weight_cancels
#print axioms RHPositiveExcessLISharpness.repeated_floor_accumulates

end RHPositiveExcessLISharpness
