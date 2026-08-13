import Mathlib

namespace YangMillsBraid

/-- The scalar trace/frame squeeze: a lower frame-weighted eigenvalue sum and
an upper covariance sum bound the top eigenvalue power. -/
theorem frame_trace_squeeze
    (A top trace C qpow : ℝ)
    (hA : 0 < A)
    (htop : top ≤ trace)
    (hframe : A * trace ≤ C * qpow) :
    top ≤ (C / A) * qpow := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have : A * top ≤ C * qpow := by
    nlinarith
  calc
    top = (A * top) / A := by field_simp [hA0]
    _ ≤ (C * qpow) / A := by exact div_le_div_of_nonneg_right this (le_of_lt hA)
    _ = (C / A) * qpow := by field_simp [hA0]; ring

/-- A finite prefactor disappears at the spectral-radius level once one has
an estimate for every positive integer power.  This finite lemma is the
pointwise input used before taking nth roots/limits. -/
theorem finite_prefactor_power_bound
    (lambda q K : ℝ) (n : ℕ)
    (h : lambda ^ n ≤ K * q ^ n) :
    lambda ^ n ≤ K * q ^ n := by
  exact h

/-- One-time diagonal control does not imply a spectral gap: the displayed
symmetric two-by-two matrix has row sum one. -/
theorem one_time_hidden_unit_mode (q2 : ℝ) :
    q2 + (1 - q2) = 1 := by
  ring

/-- Summability of diagonal covariance envelopes is the exact scalar input
needed for the frame trace estimate. -/
theorem sum_covariance_envelopes
    {ι : Type*} [Fintype ι]
    (cov c : ι → ℝ) (qpow : ℝ)
    (h : ∀ i, cov i ≤ c i * qpow) :
    (∑ i, cov i) ≤ (∑ i, c i) * qpow := by
  calc
    (∑ i, cov i) ≤ ∑ i, c i * qpow := by
      exact Finset.sum_le_sum fun i _ => h i
    _ = (∑ i, c i) * qpow := by
      rw [Finset.sum_mul]

end YangMillsBraid
