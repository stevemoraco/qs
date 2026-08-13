import Mathlib

namespace B4.Run21.RH

theorem banker_scale_distortion_transfer {x s t A K : ℝ}
    (hA : 0 ≤ A) (hx : |x| ≤ A * s) (hst : s ≤ K * t) :
    |x| ≤ (A * K) * t := by
  calc
    |x| ≤ A * s := hx
    _ ≤ A * (K * t) := mul_le_mul_of_nonneg_left hst hA
    _ = (A * K) * t := by ring

theorem critic_positive_value_rescaled_budget :
    let x : ℝ := 1
    let s : ℝ := 1
    let t : ℝ := 1 / 100
    0 < x ∧ 0 < s ∧ 0 < t ∧ x ≤ s ∧ ¬ x ≤ 10 * t := by
  norm_num

theorem cleaner_strict_scale_margin {x s t A K B : ℝ}
    (hA : 0 ≤ A) (hx : |x| ≤ A * s) (hst : s ≤ K * t)
    (hB : A * K < B) (ht : 0 < t) :
    |x| < B * t := by
  calc
    |x| ≤ A * s := hx
    _ ≤ A * (K * t) := mul_le_mul_of_nonneg_left hst hA
    _ = (A * K) * t := by ring
    _ < B * t := mul_lt_mul_of_pos_right hB ht

#print axioms banker_scale_distortion_transfer
#print axioms critic_positive_value_rescaled_budget
#print axioms cleaner_strict_scale_margin

end B4.Run21.RH
