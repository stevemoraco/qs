import Mathlib

namespace SixLaneAudit.UniformMarginFirewall

/-- A strict absolute-error bound by half of a reference value gives a strict
half-reference lower bound.  No positivity assumption on `L` is needed for
this algebraic implication. -/
theorem tail_lower_of_abs_error
    {f : ℕ → ℝ} {N : ℕ} {L : ℝ}
    (htail : ∀ n, N ≤ n → |f n - L| < L / 2) :
    ∀ n, N ≤ n → L / 2 < f n := by
  intro n hn
  have hlower := (abs_lt.mp (htail n hn)).1
  linarith

/-- Exact finite-prefix + quantitative-tail criterion for a positive uniform
margin.  The finite exceptional prefix is certified by `δ`; the infinite tail
is certified by convergence-with-margin data strong enough to place every tail
term within `L/2` of a positive reference `L`. -/
theorem finite_prefix_tail_uniform_margin
    {f : ℕ → ℝ} {N : ℕ} {δ L : ℝ}
    (hδ : 0 < δ)
    (hL : 0 < L)
    (hprefix : ∀ n, n < N → δ ≤ f n)
    (htail : ∀ n, N ≤ n → |f n - L| < L / 2) :
    0 < min δ (L / 2) ∧
      ∀ n, min δ (L / 2) ≤ f n := by
  constructor
  · have hhalf : 0 < L / 2 := by linarith
    exact lt_min hδ hhalf
  · intro n
    by_cases hn : n < N
    · exact le_trans (min_le_left _ _) (hprefix n hn)
    · have hn' : N ≤ n := Nat.le_of_not_gt hn
      have htail_lower : L / 2 < f n :=
        tail_lower_of_abs_error htail n hn'
      exact le_trans (min_le_right _ _) (le_of_lt htail_lower)

/-- The criterion implies pointwise strict positivity everywhere, but in a form
that also records a single explicit global lower bound. -/
theorem finite_prefix_tail_all_positive
    {f : ℕ → ℝ} {N : ℕ} {δ L : ℝ}
    (hδ : 0 < δ)
    (hL : 0 < L)
    (hprefix : ∀ n, n < N → δ ≤ f n)
    (htail : ∀ n, N ≤ n → |f n - L| < L / 2) :
    ∀ n, 0 < f n := by
  have hglobal :=
    finite_prefix_tail_uniform_margin hδ hL hprefix htail
  intro n
  exact lt_of_lt_of_le hglobal.1 (hglobal.2 n)

#print axioms tail_lower_of_abs_error
#print axioms finite_prefix_tail_uniform_margin
#print axioms finite_prefix_tail_all_positive

end SixLaneAudit.UniformMarginFirewall
