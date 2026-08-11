import Mathlib

/-!
# Yang--Mills compact-crossover OS slack: finite scalar core

Honesty boundary: this file formalizes only finite real-algebra identities for
propagating a connected Gram contraction factor through finitely many relative
comparison steps. It does not formalize Osterwalder--Schrader reconstruction,
Gram forms, gauge theory, renormalization, continuum limits, or Yang--Mills.
-/

namespace MillenniumBraid
namespace YMCompactOSSlack

/-- Product of zero-time norm-retention factors through the first `n` steps. -/
def retentionProduct (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 - ε j)

/-- Weighted total contraction-slack loss through the first `n` steps. -/
def weightedLoss (ε η : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, retentionProduct ε j * (ε j + η j)

@[simp] theorem retentionProduct_zero (ε : ℕ → ℝ) :
    retentionProduct ε 0 = 1 := by
  simp [retentionProduct]

@[simp] theorem retentionProduct_succ (ε : ℕ → ℝ) (n : ℕ) :
    retentionProduct ε (n + 1) =
      retentionProduct ε n * (1 - ε n) := by
  simp [retentionProduct, Finset.prod_range_succ]

@[simp] theorem weightedLoss_zero (ε η : ℕ → ℝ) :
    weightedLoss ε η 0 = 0 := by
  simp [weightedLoss]

@[simp] theorem weightedLoss_succ (ε η : ℕ → ℝ) (n : ℕ) :
    weightedLoss ε η (n + 1) =
      weightedLoss ε η n + retentionProduct ε n * (ε n + η n) := by
  simp [weightedLoss, Finset.sum_range_succ]

/-- One-step algebra: the surviving slack after the ratio update
`q' = (q + η) / (1 - ε)` obeys the cross-multiplied recurrence used by the
finite telescope. -/
theorem one_step_slack_identity
    (q q' ε η : ℝ)
    (hε : 1 - ε ≠ 0)
    (hq' : q' = (q + η) / (1 - ε)) :
    (1 - ε) * (1 - q') = (1 - q) - (ε + η) := by
  rw [hq']
  field_simp [hε]
  ring

/-- Exact finite weighted-slack telescope. The recurrence is written without
division so the identity itself does not need positivity assumptions. -/
theorem weighted_slack_identity
    (s ε η : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ j < n,
      (1 - ε j) * s (j + 1) = s j - (ε j + η j)) :
    retentionProduct ε n * s n = s 0 - weightedLoss ε η n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : ∀ j < n,
          (1 - ε j) * s (j + 1) = s j - (ε j + η j) := by
        intro j hj
        exact hrec j (Nat.lt_succ_of_lt hj)
      have hih := ih hprev
      have hn := hrec n (Nat.lt_succ_self n)
      rw [retentionProduct_succ, weightedLoss_succ]
      calc
        (retentionProduct ε n * (1 - ε n)) * s (n + 1) =
            retentionProduct ε n * ((1 - ε n) * s (n + 1)) := by ring
        _ = retentionProduct ε n * (s n - (ε n + η n)) := by rw [hn]
        _ = retentionProduct ε n * s n -
            retentionProduct ε n * (ε n + η n) := by ring
        _ = (s 0 - weightedLoss ε η n) -
            retentionProduct ε n * (ε n + η n) := by rw [hih]
        _ = s 0 - (weightedLoss ε η n +
            retentionProduct ε n * (ε n + η n)) := by ring

/-- Positive cumulative retention and a strict weighted-loss budget force
positive final slack. -/
theorem final_slack_positive
    (s ε η : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ j < n,
      (1 - ε j) * s (j + 1) = s j - (ε j + η j))
    (hret : 0 < retentionProduct ε n)
    (hbudget : weightedLoss ε η n < s 0) :
    0 < s n := by
  have hid := weighted_slack_identity s ε η n hrec
  have hprod : 0 < retentionProduct ε n * s n := by
    rw [hid]
    linarith
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · linarith

/-- If the final slack is `1 - q`, positivity is exactly strict contraction. -/
theorem final_factor_lt_one
    (s ε η : ℕ → ℝ) (n : ℕ) (q : ℝ)
    (hrec : ∀ j < n,
      (1 - ε j) * s (j + 1) = s j - (ε j + η j))
    (hret : 0 < retentionProduct ε n)
    (hbudget : weightedLoss ε η n < s 0)
    (hfinal : s n = 1 - q) :
    q < 1 := by
  have hs := final_slack_positive s ε η n hrec hret hbudget
  rw [hfinal] at hs
  linarith

/-- Exact product-loss identity `1 - P_n = Σ_{j<n} P_j ε_j`. -/
theorem one_sub_retentionProduct
    (ε : ℕ → ℝ) (n : ℕ) :
    1 - retentionProduct ε n =
      ∑ j ∈ Finset.range n, retentionProduct ε j * ε j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [retentionProduct_succ, Finset.sum_range_succ, ← ih]
      ring

#print axioms retentionProduct_zero
#print axioms retentionProduct_succ
#print axioms weightedLoss_zero
#print axioms weightedLoss_succ
#print axioms one_step_slack_identity
#print axioms weighted_slack_identity
#print axioms final_slack_positive
#print axioms final_factor_lt_one
#print axioms one_sub_retentionProduct

end YMCompactOSSlack
end MillenniumBraid