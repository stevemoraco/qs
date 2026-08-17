import Mathlib

namespace YMGapTube

theorem finite_loss_does_not_force_positive_remainder :
    ∃ (Delta0 totalLoss : ℝ),
      0 < Delta0 ∧ 0 ≤ totalLoss ∧ ¬ (0 < Delta0 - totalLoss) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  norm_num

theorem positive_remainder_of_totalLoss_lt_initial
    (Delta0 totalLoss : ℝ) (h : totalLoss < Delta0) :
    0 < Delta0 - totalLoss := by
  linarith

theorem nonnegative_gap_does_not_bound_exponential_by_unit_gap :
    ∃ (a Delta : ℝ),
      0 < a ∧ 0 ≤ Delta ∧ Real.exp a < Real.exp (a * Delta) := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  apply Real.exp_lt_exp.mpr
  norm_num

theorem quadratic_transfer_tube_step
    (q qnext r delta : ℝ)
    (hq0 : 0 ≤ q) (hqr : q ≤ r) (_hr0 : 0 ≤ r)
    (hstep : qnext ≤ q ^ 2 + delta)
    (htube : r ^ 2 + delta ≤ r) :
    qnext ≤ r := by
  have hsq : q ^ 2 ≤ r ^ 2 := by nlinarith
  linarith

theorem quadratic_transfer_tube_all_scales
    (q : ℕ → ℝ) (r delta : ℝ)
    (hr0 : 0 ≤ r)
    (hqnonneg : ∀ k, 0 ≤ q k)
    (hq0 : q 0 ≤ r)
    (hstep : ∀ k, q (k + 1) ≤ (q k) ^ 2 + delta)
    (htube : r ^ 2 + delta ≤ r) :
    ∀ k, q k ≤ r := by
  intro k
  induction k with
  | zero => exact hq0
  | succ k ih =>
      exact quadratic_transfer_tube_step
        (q k) (q (k + 1)) r delta (hqnonneg k) ih hr0 (hstep k) htube

theorem half_tube_of_quarter_defect
    (q : ℕ → ℝ) (delta : ℝ)
    (hqnonneg : ∀ k, 0 ≤ q k)
    (hq0 : q 0 ≤ (1 / 2 : ℝ))
    (hstep : ∀ k, q (k + 1) ≤ (q k) ^ 2 + delta)
    (hdelta : delta ≤ (1 / 4 : ℝ)) :
    ∀ k, q k ≤ (1 / 2 : ℝ) := by
  apply quadratic_transfer_tube_all_scales q (1 / 2) delta
  · norm_num
  · exact hqnonneg
  · exact hq0
  · exact hstep
  · norm_num at hdelta ⊢
    linarith

theorem quadratic_transfer_tube_from_scale
    (q delta : ℕ → ℝ) (K : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r)
    (hqnonneg : ∀ k, K ≤ k → 0 ≤ q k)
    (hentry : q K ≤ r)
    (hstep : ∀ k, K ≤ k → q (k + 1) ≤ (q k) ^ 2 + delta k)
    (hdefect : ∀ k, K ≤ k → r ^ 2 + delta k ≤ r) :
    ∀ k, K ≤ k → q k ≤ r := by
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction n with
  | zero => simpa using hentry
  | succ n ih =>
      have hKn : K ≤ K + n := Nat.le_add_right K n
      have hn0 : 0 ≤ q (K + n) := hqnonneg (K + n) hKn
      have hir : q (K + n) ≤ r := ih hKn
      have hs := hstep (K + n) hKn
      have hd := hdefect (K + n) hKn
      have hout := quadratic_transfer_tube_step
        (q (K + n)) (q (K + n + 1)) r (delta (K + n))
        hn0 hir hr0 hs hd
      simpa [Nat.add_assoc] using hout

theorem half_transfer_tube_from_scale
    (q delta : ℕ → ℝ) (K : ℕ)
    (hqnonneg : ∀ k, K ≤ k → 0 ≤ q k)
    (hentry : q K ≤ (1 / 2 : ℝ))
    (hstep : ∀ k, K ≤ k → q (k + 1) ≤ (q k) ^ 2 + delta k)
    (hdefect : ∀ k, K ≤ k → delta k ≤ (1 / 4 : ℝ)) :
    ∀ k, K ≤ k → q k ≤ (1 / 2 : ℝ) := by
  apply quadratic_transfer_tube_from_scale q delta K (1 / 2)
  · norm_num
  · exact hqnonneg
  · exact hentry
  · exact hstep
  · intro k hk
    have hd := hdefect k hk
    norm_num at hd ⊢
    linarith

/-- The full two-cell rank-one Gram form is PSD. -/
theorem two_cell_full_gram_psd (x y : ℝ) :
    0 ≤ x ^ 2 + 2 * x * y + y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

/-- Keeping only the cross-cell entries of that PSD Gram matrix is not PSD. -/
theorem mixed_pair_mask_can_be_negative :
    ∃ (x y : ℝ), 2 * x * y < 0 := by
  refine ⟨1, -1, ?_⟩
  norm_num

/-- Thus PSD of a full Gram matrix does not survive the off-diagonal/mixed-pair mask. -/
theorem psd_not_preserved_by_mixed_pair_mask :
    ¬ (∀ (x y : ℝ),
      0 ≤ x ^ 2 + 2 * x * y + y ^ 2 → 0 ≤ 2 * x * y) := by
  intro h
  have hbad := h 1 (-1) (by norm_num)
  norm_num at hbad

/-- A PSD form need not leave a PSD remainder after one principal coordinate block is peeled off. -/
theorem principal_block_remainder_can_be_negative :
    ∃ (x y : ℝ), (x + y) ^ 2 - x ^ 2 < 0 := by
  refine ⟨-1, 1, ?_⟩
  norm_num

#print axioms finite_loss_does_not_force_positive_remainder
#print axioms positive_remainder_of_totalLoss_lt_initial
#print axioms nonnegative_gap_does_not_bound_exponential_by_unit_gap
#print axioms quadratic_transfer_tube_step
#print axioms quadratic_transfer_tube_all_scales
#print axioms half_tube_of_quarter_defect
#print axioms quadratic_transfer_tube_from_scale
#print axioms half_transfer_tube_from_scale
#print axioms two_cell_full_gram_psd
#print axioms mixed_pair_mask_can_be_negative
#print axioms psd_not_preserved_by_mixed_pair_mask
#print axioms principal_block_remainder_can_be_negative

end YMGapTube
