import Mathlib

namespace MillenniumRun14

/-- Iterating one-step forward gap losses gives the exact cumulative defect budget.
This is the direction used when a lower bound is known at the fine scale and
propagated to coarser scales. -/
theorem ym_cumulative_gap_budget
    (m d : ℕ → ℝ)
    (hstep : ∀ k, m (k + 1) ≥ m k - d k) :
    ∀ n, m n ≥ m 0 - ∑ k ∈ Finset.range n, d k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ]
      norm_num at hs ⊢
      linarith

/-- Iterating one-step reverse gap losses gives the cumulative budget needed
when a lower bound is known at a coarse anchor and must be propagated back to
a finer cutoff. -/
theorem ym_reverse_cumulative_gap_budget
    (m d : ℕ → ℝ)
    (hstep : ∀ k, m k ≥ m (k + 1) - d k) :
    ∀ n, m 0 ≥ m n - ∑ k ∈ Finset.range n, d k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ]
      norm_num at hs ⊢
      linarith

/-- A dimensional-transmutation scale survives a finite loss budget exactly as
needed by the Yang--Mills gap bridge: if the anchor gap is at least `c₀ Λ` and
the accumulated physical gap loss is at most `(c₀-c) Λ`, then the surviving
gap is at least `c Λ`.  This is finite algebra only; it does not supply the
nonperturbative estimates needed to bound the losses. -/
theorem ym_lambda_gap_survives_budget
    (Λ c₀ c m₀ mₙ loss : ℝ)
    (hanchor : c₀ * Λ ≤ m₀)
    (hpropagate : m₀ - loss ≤ mₙ)
    (hloss : loss ≤ (c₀ - c) * Λ) :
    c * Λ ≤ mₙ := by
  nlinarith

/-- Sequence-level version of `ym_lambda_gap_survives_budget`: one-step gap
losses plus a `Λ`-scaled total budget give a uniform lower bound at every
specified blocking depth.  The constants are deliberately regulator-agnostic;
proving the hypotheses uniformly in cutoff and volume is the live analytic
Yang--Mills problem, not part of this finite lemma. -/
theorem ym_lambda_scaled_cumulative_gap
    (m d : ℕ → ℝ)
    (Λ c₀ c : ℝ)
    (n : ℕ)
    (hstep : ∀ k, m (k + 1) ≥ m k - d k)
    (hanchor : c₀ * Λ ≤ m 0)
    (hloss : (∑ k ∈ Finset.range n, d k) ≤ (c₀ - c) * Λ) :
    c * Λ ≤ m n := by
  have hbudget := ym_cumulative_gap_budget m d hstep n
  exact ym_lambda_gap_survives_budget Λ c₀ c (m 0) (m n)
    (∑ k ∈ Finset.range n, d k) hanchor hbudget hloss

end MillenniumRun14
