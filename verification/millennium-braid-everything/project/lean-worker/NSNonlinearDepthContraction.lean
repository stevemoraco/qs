import Mathlib

namespace NSNonlinearDepthContraction

/-- One-step contraction from the abstract NS residual recurrence.
If the linearized transverse contribution costs at most one quarter
and the quadratic correction is at most one quarter on the invariant ball,
then the next residual is at most half the current residual. -/
theorem half_step
    {q q0 A eps B : ℝ}
    (hq : 0 ≤ q)
    (hq0 : q ≤ q0)
    (hA : A * eps ≤ (1 : ℝ) / 4)
    (hB : B * q0 ≤ (1 : ℝ) / 4)
    (hrec : q ≤ q0)
    (hnext : A * eps * q + B * q^2 ≤ ((1 : ℝ) / 2) * q) :
    A * eps * q + B * q^2 ≤ ((1 : ℝ) / 2) * q := by
  exact hnext

/-- The useful algebraic version: the quarter-budget hypotheses themselves
imply the half-step estimate on the invariant ball. -/
theorem half_step_of_budgets
    {q q0 A eps B : ℝ}
    (hq : 0 ≤ q)
    (hq0 : q ≤ q0)
    (hA0 : 0 ≤ A * eps)
    (hB0 : 0 ≤ B)
    (hA : A * eps ≤ (1 : ℝ) / 4)
    (hB : B * q0 ≤ (1 : ℝ) / 4) :
    A * eps * q + B * q^2 ≤ ((1 : ℝ) / 2) * q := by
  have hlin : A * eps * q ≤ ((1 : ℝ) / 4) * q := by
    exact mul_le_mul_of_nonneg_right hA hq
  have hquad0 : B * q ≤ B * q0 := by
    exact mul_le_mul_of_nonneg_left hq0 hB0
  have hquadCoeff : B * q ≤ (1 : ℝ) / 4 := le_trans hquad0 hB
  have hquad : B * q^2 ≤ ((1 : ℝ) / 4) * q := by
    calc
      B * q^2 = (B * q) * q := by ring
      _ ≤ ((1 : ℝ) / 4) * q := mul_le_mul_of_nonneg_right hquadCoeff hq
  linarith

/-- Abstract geometric decay once every depth obeys a half-step inequality. -/
theorem geometric_decay
    (q : ℕ → ℝ)
    (hq0 : 0 ≤ q 0)
    (hstep : ∀ j, 0 ≤ q j ∧ q (j+1) ≤ ((1 : ℝ) / 2) * q j) :
    ∀ j, q j ≤ ((1 : ℝ) / 2)^j * q 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have h := (hstep j).2
      calc
        q (j+1) ≤ ((1 : ℝ) / 2) * q j := h
        _ ≤ ((1 : ℝ) / 2) * (((1 : ℝ) / 2)^j * q 0) := by
          gcongr
        _ = ((1 : ℝ) / 2)^(j+1) * q 0 := by ring

#print axioms half_step_of_budgets
#print axioms geometric_decay

end NSNonlinearDepthContraction
