import Mathlib

namespace YMRegionalEnergyCover

theorem transfer_margin
    {C V D K h tau v : ℝ} {N : ℕ}
    (hbase : V - (N : ℝ) * D ≤ C)
    (hdefect : D ≤ K * h * V)
    (htau : tau = (N : ℝ) * h)
    (hV : v ≤ V)
    (hVnonneg : 0 ≤ V)
    (hrate : K * tau ≤ (1 : ℝ) / 2) :
    v / 2 ≤ C := by
  have hND : (N : ℝ) * D ≤ (N : ℝ) * (K * h * V) :=
    mul_le_mul_of_nonneg_left hdefect (Nat.cast_nonneg N)
  have hrewrite : (N : ℝ) * (K * h * V) = (K * tau) * V := by
    rw [htau]
    ring
  rw [hrewrite] at hND
  have hhalf : (K * tau) * V ≤ ((1 : ℝ) / 2) * V :=
    mul_le_mul_of_nonneg_right hrate hVnonneg
  linarith

theorem regional_sum_margin
    {α : Type*} {m : ℕ}
    (corr variance defect : α → Fin m → ℝ)
    (K h tau v : ℝ) (N : ℕ)
    (htau : tau = (N : ℝ) * h)
    (hrate : K * tau ≤ (1 : ℝ) / 2)
    (hcorr_nonneg : ∀ x i, 0 ≤ corr x i)
    (hvariance_nonneg : ∀ x i, 0 ≤ variance x i)
    (hlocal : ∀ x, ∃ i,
      v ≤ variance x i ∧
      variance x i - (N : ℝ) * defect x i ≤ corr x i ∧
      defect x i ≤ K * h * variance x i) :
    ∀ x, v / 2 ≤ ∑ i, corr x i := by
  intro x
  rcases hlocal x with ⟨i, hvi, hbase, hdefect⟩
  have hi : v / 2 ≤ corr x i :=
    transfer_margin hbase hdefect htau hvi (hvariance_nonneg x i) hrate
  have hsingle : corr x i ≤ ∑ j, corr x j := by
    exact Finset.single_le_sum
      (fun j _ => hcorr_nonneg x j) (Finset.mem_univ i)
  exact hi.trans hsingle

theorem validated_defect_bound
    {Dupper K h Vlower D V : ℝ}
    (hD : D ≤ Dupper)
    (hbudget : Dupper ≤ K * h * Vlower)
    (hV : Vlower ≤ V)
    (hKh : 0 ≤ K * h) :
    D ≤ K * h * V := by
  have hscale : K * h * Vlower ≤ K * h * V := by
    exact mul_le_mul_of_nonneg_left hV hKh
  exact hD.trans (hbudget.trans hscale)

theorem strict_margin
    {C V D K h tau v : ℝ} {N : ℕ}
    (hbase : V - (N : ℝ) * D ≤ C)
    (hdefect : D ≤ K * h * V)
    (htau : tau = (N : ℝ) * h)
    (hv : 0 < v)
    (hV : v ≤ V)
    (hrate : K * tau ≤ (1 : ℝ) / 2) :
    0 < C := by
  have hVnonneg : 0 ≤ V := le_trans (le_of_lt hv) hV
  have hmargin : v / 2 ≤ C :=
    transfer_margin hbase hdefect htau hV hVnonneg hrate
  exact lt_of_lt_of_le (half_pos hv) hmargin

#print axioms transfer_margin
#print axioms regional_sum_margin
#print axioms validated_defect_bound
#print axioms strict_margin

end YMRegionalEnergyCover
