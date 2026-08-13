import Mathlib

namespace FloorFiber

def fiber (N m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun k => N / k = m)

theorem three_two_empty : fiber 3 2 = ∅ := by
  decide

theorem three_two_weight_zero :
    (∑ k ∈ fiber 3 2, (k : ℚ) / 3) = 0 := by
  rw [three_two_empty]
  simp

theorem positive_threshold_failure :
    (∑ k ∈ fiber 3 2, (k : ℚ) / 3) < 1 / (2 * (2 : ℚ)) := by
  rw [three_two_weight_zero]
  norm_num

theorem range_not_surjective :
    ¬ (∀ m : ℕ, m ∈ Finset.Icc 1 3 →
          ∃ k : ℕ, k ∈ Finset.Icc 1 3 ∧ 3 / k = m) := by
  intro h
  obtain ⟨k, hk, hdiv⟩ := h 2 (by norm_num)
  interval_cases k <;> norm_num at hk hdiv

theorem corrected_scale_has_witness (m : ℕ) (hm : 0 < m) :
    m + 1 ∈ fiber (m * (m + 1)) m := by
  simp only [fiber, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · omega
  constructor
  · nlinarith
  · exact Nat.mul_div_right m (m + 1)

#print axioms FloorFiber.three_two_empty
#print axioms FloorFiber.three_two_weight_zero
#print axioms FloorFiber.positive_threshold_failure
#print axioms FloorFiber.range_not_surjective
#print axioms FloorFiber.corrected_scale_has_witness

end FloorFiber
