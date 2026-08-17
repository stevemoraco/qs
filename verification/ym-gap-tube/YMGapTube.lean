import Mathlib

namespace YMGapTube

/-- Positive initial gap plus finite nonnegative total loss does not force a
strictly positive remainder. -/
theorem finite_loss_does_not_force_positive_remainder :
    ∃ (Delta0 totalLoss : ℝ),
      0 < Delta0 ∧ 0 ≤ totalLoss ∧ ¬ (0 < Delta0 - totalLoss) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  norm_num

/-- The missing strict total-loss margin is sufficient. -/
theorem positive_remainder_of_totalLoss_lt_initial
    (Delta0 totalLoss : ℝ)
    (h : totalLoss < Delta0) :
    0 < Delta0 - totalLoss := by
  linarith

/-- Nonnegativity of Delta alone does not justify exp(a*Delta) ≤ exp(a). -/
theorem nonnegative_gap_does_not_bound_exponential_by_unit_gap :
    ∃ (a Delta : ℝ),
      0 < a ∧ 0 ≤ Delta ∧ Real.exp a < Real.exp (a * Delta) := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  apply Real.exp_lt_exp.mpr
  norm_num

/-- One normalized quadratic transfer step preserves [0,r] when the defect
fits inside the tube margin. -/
theorem quadratic_transfer_tube_step
    (q qnext r delta : ℝ)
    (hq0 : 0 ≤ q) (hqr : q ≤ r) (hr0 : 0 ≤ r)
    (hstep : qnext ≤ q ^ 2 + delta)
    (htube : r ^ 2 + delta ≤ r) :
    qnext ≤ r := by
  have hsq : q ^ 2 ≤ r ^ 2 := by nlinarith
  linarith

/-- The normalized transfer tube is invariant at every discrete scale. -/
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

/-- Concrete fixed tube: a defect at most 1/4 preserves q≤1/2. -/
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

#print axioms finite_loss_does_not_force_positive_remainder
#print axioms positive_remainder_of_totalLoss_lt_initial
#print axioms nonnegative_gap_does_not_bound_exponential_by_unit_gap
#print axioms quadratic_transfer_tube_step
#print axioms quadratic_transfer_tube_all_scales
#print axioms half_tube_of_quarter_defect

end YMGapTube
