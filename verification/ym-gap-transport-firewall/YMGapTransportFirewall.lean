import Mathlib

namespace YMGapTransportFirewall

/-- A diagonal quadratic form with vacuum coefficient one and excited
coefficient zero.  It models a transfer operator with unit transfer gap. -/
def fineForm (v : ℝ × ℝ) : ℝ := v.1 ^ 2

/-- A diagonal quadratic form with the same vacuum coefficient and excited
coefficient `1 - ε`.  Its transfer gap is exactly `ε`. -/
def coarseForm (ε : ℝ) (v : ℝ × ℝ) : ℝ :=
  v.1 ^ 2 + (1 - ε) * v.2 ^ 2

/-- Lower quadratic-form domination permits the excited eigenvalue to move
arbitrarily close to the vacuum eigenvalue. -/
theorem fineForm_le_coarseForm {ε : ℝ} (hε : ε ≤ 1) (v : ℝ × ℝ) :
    fineForm v ≤ coarseForm ε v := by
  have hcoef : 0 ≤ 1 - ε := sub_nonneg.mpr hε
  have hterm : 0 ≤ (1 - ε) * v.2 ^ 2 :=
    mul_nonneg hcoef (sq_nonneg v.2)
  simp only [fineForm, coarseForm]
  linarith

/-- Exact excited-state transfer gap of the coarse diagonal model. -/
theorem coarseForm_gap (ε : ℝ) :
    1 - coarseForm ε (0, 1) = ε := by
  simp [coarseForm]

/-- For every positive `ε ≤ 1`, the coarse form dominates the fine form from
below while its transfer gap is only `ε`.  Thus a lower Loewner inequality has
no positive gap-preservation modulus depending only on the fine gap. -/
theorem lower_order_allows_arbitrarily_small_gap
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ v : ℝ × ℝ, fineForm v ≤ coarseForm ε v) ∧
      0 < 1 - coarseForm ε (0, 1) ∧
      1 - coarseForm ε (0, 1) = ε := by
  refine ⟨fun v => fineForm_le_coarseForm hε1 v, ?_, coarseForm_gap ε⟩
  simpa [coarseForm] using hε0

/-- The precise failed inference: lower domination does not imply the upper
quadratic-form estimate needed to control the second eigenvalue. -/
theorem lower_order_does_not_imply_upper_order :
    (∀ v : ℝ × ℝ, fineForm v ≤ coarseForm (1 / 2 : ℝ) v) ∧
      ¬ (∀ v : ℝ × ℝ, coarseForm (1 / 2 : ℝ) v ≤ fineForm v) := by
  constructor
  · intro v
    exact fineForm_le_coarseForm (by norm_num) v
  · intro hupper
    have h := hupper (0, 1)
    norm_num [fineForm, coarseForm] at h

/-- The correct transfer-gap arithmetic starts from upper domination of the
excited transfer eigenvalue. -/
theorem upper_order_gap_salvage
    (λFine λCoarse ε : ℝ)
    (hupper : λCoarse ≤ λFine + ε) :
    1 - λFine - ε ≤ 1 - λCoarse := by
  linarith

/-- One finite defect can exhaust the whole initial gap while satisfying the
one-step telescoping inequality. -/
theorem one_step_defect_can_exhaust_gap :
    ∃ Δ₀ Δ₁ ε₀ : ℝ,
      0 < Δ₀ ∧ 0 ≤ Δ₁ ∧ 0 ≤ ε₀ ∧
      Δ₀ - ε₀ ≤ Δ₁ ∧ ¬ 0 < Δ₀ - ε₀ := by
  refine ⟨1, 0, 1, ?_⟩
  norm_num

/-- Even a nonnegative finite defect sum may equal the initial gap, so
finiteness alone does not imply a positive residual budget. -/
theorem finite_sum_can_exhaust_initial_gap :
    ∃ (Δ₀ : ℝ) (ε : Fin 1 → ℝ),
      0 < Δ₀ ∧ (∀ i, 0 ≤ ε i) ∧
      (∑ i, ε i) = Δ₀ ∧
      ¬ 0 < Δ₀ - ∑ i, ε i := by
  refine ⟨1, fun _ => 1, by norm_num, ?_, ?_, ?_⟩
  · intro i
    norm_num
  · simp
  · simp

/-- Exact finite telescoping inequality.  This is what defect summability
actually gives before a separate strict-smallness hypothesis is supplied. -/
theorem finite_defect_telescoping
    (Δ ε : ℕ → ℝ)
    (hstep : ∀ k, Δ k - ε k ≤ Δ (k + 1)) :
    ∀ n, Δ 0 - ∑ k ∈ Finset.range n, ε k ≤ Δ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Δ 0 - ∑ k ∈ Finset.range (n + 1), ε k =
            (Δ 0 - ∑ k ∈ Finset.range n, ε k) - ε n := by
              rw [Finset.sum_range_succ]
              ring
        _ ≤ Δ n - ε n := sub_le_sub_right ih (ε n)
        _ ≤ Δ (n + 1) := hstep n

/-- Correct salvage: a strict total-defect budget below the initial gap gives a
strictly positive finite-stage gap. -/
theorem positive_gap_of_strict_finite_budget
    (Δ ε : ℕ → ℝ)
    (hstep : ∀ k, Δ k - ε k ≤ Δ (k + 1))
    (n : ℕ)
    (hbudget : (∑ k ∈ Finset.range n, ε k) < Δ 0) :
    0 < Δ n := by
  exact lt_of_lt_of_le (sub_pos.mpr hbudget)
    (finite_defect_telescoping Δ ε hstep n)

/-- Positivity of a subtracted operator does not permit dropping that
subtraction inside a vector norm.  The one-dimensional Hilbert-space model
`A = 0`, `D = 1`, `E = 0` already contradicts the claimed norm estimate. -/
theorem positive_subtraction_norm_countermodel :
    ∃ A D E : ℝ,
      0 ≤ D ∧ |A - D + E| > |A| + |E| := by
  refine ⟨0, 1, 0, ?_⟩
  norm_num

/-- A positive semidefinite two-coordinate Gram form. -/
def gramForm (v : ℝ × ℝ) : ℝ := (v.1 + v.2) ^ 2

/-- Its off-diagonal part. -/
def offDiagonalForm (v : ℝ × ℝ) : ℝ := 2 * v.1 * v.2

/-- Positivity of the full Gram form does not make the off-diagonal part
positive. -/
theorem positive_gram_offDiagonal_indefinite :
    (∀ v : ℝ × ℝ, 0 ≤ gramForm v) ∧
      ∃ v : ℝ × ℝ, offDiagonalForm v < 0 := by
  constructor
  · intro v
    exact sq_nonneg (v.1 + v.2)
  · refine ⟨(1, -1), ?_⟩
    norm_num [offDiagonalForm]

/-- Nonnegativity of a physical gap does not imply the exponential estimate
`exp (a * Δ) ≤ exp a`; the missing hypothesis is `Δ ≤ 1`. -/
theorem nonnegative_gap_does_not_bound_exponential :
    ¬ (∀ a Δ : ℝ, 0 ≤ a → 0 ≤ Δ →
        Real.exp (a * Δ) ≤ Real.exp a) := by
  intro h
  have hbad := h 1 2 (by norm_num) (by norm_num)
  have hbad' : Real.exp 2 ≤ Real.exp 1 := by
    simpa using hbad
  have hstrict : Real.exp 1 < Real.exp 2 :=
    Real.exp_lt_exp.mpr (by norm_num)
  exact (not_le_of_gt hstrict) hbad'

end YMGapTransportFirewall
