import Mathlib

namespace B4.Run22.PNP

theorem banker_quadratic_padding_transfer {n m T K C : ℝ}
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hpad : m ≤ K * n) (hT : T ≤ C * m ^ 2) :
    T ≤ C * (K * n) ^ 2 := by
  have hKn : 0 ≤ K * n := mul_nonneg hK hn
  have hprod : 0 ≤ (K * n - m) * (K * n + m) :=
    mul_nonneg (sub_nonneg.mpr hpad) (add_nonneg hKn hm)
  have hm2 : m ^ 2 ≤ (K * n) ^ 2 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hm2 hC
  exact le_trans hT hscaled

theorem critic_runtime_in_padded_length_needs_distortion_bound :
    ∃ n m T : ℝ,
      0 < n ∧ 0 < m ∧ T ≤ m ^ 2 ∧ 10 * n ^ 2 < T := by
  exact ⟨1, 100, 10000, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem cleaner_original_quadratic_class {n m T K C D : ℝ}
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hpad : m ≤ K * n) (hT : T ≤ C * m ^ 2)
    (hcoef : C * K ^ 2 ≤ D) :
    T ≤ D * n ^ 2 := by
  have h := banker_quadratic_padding_transfer hn hm hK hC hpad hT
  have hrewrite : C * (K * n) ^ 2 = (C * K ^ 2) * n ^ 2 := by ring
  rw [hrewrite] at h
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hcap := mul_le_mul_of_nonneg_right hcoef hn2
  exact le_trans h hcap

#print axioms banker_quadratic_padding_transfer
#print axioms critic_runtime_in_padded_length_needs_distortion_bound
#print axioms cleaner_original_quadratic_class

end B4.Run22.PNP
