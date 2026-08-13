import Mathlib

namespace Millennium.YangMills

def physicalRateFromStepExponent (a mStep : ℝ) : ℝ := mStep / a

theorem physicalGap_of_stepExponent
    {a mStep E : ℝ} (ha : 0 < a) (hstep : mStep ≤ a * E) :
    physicalRateFromStepExponent a mStep ≤ E := by
  rw [physicalRateFromStepExponent]
  exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hstep)

theorem stepExponent_eq_physicalExponent
    {a mStep n : ℝ} (ha : a ≠ 0) :
    mStep * n = physicalRateFromStepExponent a mStep * (a * n) := by
  simp [physicalRateFromStepExponent, ha]
  ring

theorem sameNumericGapInference_false :
    ∃ a mStep E : ℝ,
      0 < a ∧ 0 < mStep ∧ mStep ≤ a * E ∧ E < mStep := by
  refine ⟨2, 1, (3 : ℝ) / 4, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem concrete_exponent_witness :
    (1 : ℝ) ≤ 2 * ((3 : ℝ) / 4) ∧ ((3 : ℝ) / 4) < 1 := by
  norm_num

#print axioms physicalRateFromStepExponent
#print axioms physicalGap_of_stepExponent
#print axioms stepExponent_eq_physicalExponent
#print axioms sameNumericGapInference_false
#print axioms concrete_exponent_witness

end Millennium.YangMills
