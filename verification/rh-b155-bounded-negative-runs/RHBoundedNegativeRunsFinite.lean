import Mathlib

/-!
# RH B155 bounded-negative-run finite core

Finite real/order/quantifier algebra only.

This file formalizes the deterministic shell used by the human B155 reduction:

* a sufficiently deep left value remains negative through any fixed finite run
  when each later sample pays a bounded per-step interpolation error;
* the exact two-sample logical shadow of `negative index <= 1`;
* a positive two-point stencil is negative when both inputs are negative;
* arbitrarily long negative runs are incompatible with any eventual fixed-window
  nonnegativity property;
* eventual pointwise nonnegativity implies an eventual fixed-window property;
* the exact forward-square polynomial identity.

It does **not** formalize Bhattacharya--Martin--Simpson, Mertens' theorem,
prime sums, logarithmic integrals, zeta, BGST/Hermite matrices, or RH.
-/

namespace RHBoundedNegativeRunsFinite

/-- Exact physical displacement from one square coordinate to a later one. -/
theorem square_forward_gap (n j : ℝ) :
    (n + j) ^ 2 - n ^ 2 = 2 * n * j + j ^ 2 := by
  ring

/-- A fixed interpolation-error budget cannot overturn a sufficiently deep
negative left endpoint anywhere in the finite run. -/
theorem deep_left_value_forces_negative_run
    (r : ℕ) (x : ℕ → ℝ) (x0 E : ℝ)
    (hE : 0 ≤ E)
    (hdeep : x0 + (r : ℝ) * E < 0)
    (htransport : ∀ j : ℕ, j < r → x j ≤ x0 + (j : ℝ) * E) :
    ∀ j : ℕ, j < r → x j < 0 := by
  intro j hj
  have hjr_nat : j ≤ r := Nat.le_of_lt hj
  have hjr : (j : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr_nat
  have hmul : (j : ℝ) * E ≤ (r : ℝ) * E :=
    mul_le_mul_of_nonneg_right hjr hE
  exact lt_of_le_of_lt (htransport j hj) (by linarith)

/-- Two real samples contain a nonnegative value exactly when they are not both
strictly negative. This is the scalar shadow of the two-dimensional condition
`n_- <= 1`. -/
theorem two_window_has_nonnegative_iff_not_both_negative (a b : ℝ) :
    (0 ≤ a ∨ 0 ≤ b) ↔ ¬ (a < 0 ∧ b < 0) := by
  constructor
  · intro h hab
    rcases h with ha | hb
    · exact (not_lt_of_ge ha) hab.1
    · exact (not_lt_of_ge hb) hab.2
  · intro h
    by_cases ha : 0 ≤ a
    · exact Or.inl ha
    · have hna : a < 0 := lt_of_not_ge ha
      right
      by_contra hb
      have hnb : b < 0 := lt_of_not_ge hb
      exact h ⟨hna, hnb⟩

/-- Every positive two-point stencil is negative on a completely negative
window. -/
theorem positive_two_stencil_negative
    {w0 w1 a b : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1)
    (ha : a < 0) (hb : b < 0) :
    w0 * a + w1 * b < 0 := by
  exact add_neg (mul_neg_of_pos_of_neg hw0 ha) (mul_neg_of_pos_of_neg hw1 hb)

/-- Abstract source-side property: negative runs of every fixed finite length
occur arbitrarily far out. -/
def ArbitrarilyLongNegativeRuns (x : ℕ → ℝ) : Prop :=
  ∀ r N : ℕ, 0 < r → ∃ n : ℕ, N ≤ n ∧ ∀ j : ℕ, j < r → x (n + j) < 0

/-- Abstract target-side property: some fixed finite window eventually always
contains a nonnegative sample. -/
def EventuallyFixedWindowNonnegative (x : ℕ → ℝ) : Prop :=
  ∃ r N : ℕ, 0 < r ∧ ∀ n : ℕ, N ≤ n → ∃ j : ℕ, j < r ∧ 0 ≤ x (n + j)

/-- Arbitrarily long negative runs rule out every eventual fixed-window
nonnegativity certificate. -/
theorem arbitrarily_long_runs_forbid_fixed_window
    (x : ℕ → ℝ)
    (hneg : ArbitrarilyLongNegativeRuns x) :
    ¬ EventuallyFixedWindowNonnegative x := by
  rintro ⟨r, N, hr, hwindow⟩
  obtain ⟨n, hn, hallneg⟩ := hneg r N hr
  obtain ⟨j, hj, hjnonneg⟩ := hwindow n hn
  exact (not_lt_of_ge hjnonneg) (hallneg j hj)

/-- Eventual pointwise nonnegativity supplies the fixed-window property with
window length one. -/
theorem eventual_pointwise_nonnegative_gives_fixed_window
    (x : ℕ → ℝ)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ x n) :
    EventuallyFixedWindowNonnegative x := by
  obtain ⟨N, hN⟩ := h
  refine ⟨1, N, by omega, ?_⟩
  intro n hn
  refine ⟨0, by omega, ?_⟩
  simpa using hN n hn

#print axioms square_forward_gap
#print axioms deep_left_value_forces_negative_run
#print axioms two_window_has_nonnegative_iff_not_both_negative
#print axioms positive_two_stencil_negative
#print axioms arbitrarily_long_runs_forbid_fixed_window
#print axioms eventual_pointwise_nonnegative_gives_fixed_window

end RHBoundedNegativeRunsFinite
