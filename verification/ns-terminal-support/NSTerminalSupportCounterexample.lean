import Mathlib

namespace NSTerminalSupportCounterexample

/-- Activation times for the human counterexample.  Only `activation 0 = 0`
is needed by the finite logical core below. -/
noncomputable def activation (k : ℕ) : ℝ :=
  1 - ((1 : ℝ) / 2) ^ k

/-- One persistent early residual and an identically zero large-index tail. -/
def residual (k : ℕ) (_t : ℝ) : ℝ :=
  if k = 0 then 1 else 0

/-- Future support on the physical time half-line.  This formulation records
exactly the implication used in the audited closure argument: before the
activation time, the residual vanishes. -/
def FutureSupportedOnHalfLine
    (E : ℕ → ℝ → ℝ)
    (t0 : ℕ → ℝ) : Prop :=
  ∀ k t, 0 ≤ t → t < t0 k → E k t = 0

/-- The counterexample satisfies the stated future-support condition.  At the
zeroth shell the condition is vacuous on `t ≥ 0`, because `t_0 = 0`; all later
shells are identically zero. -/
theorem residual_future_supported :
    FutureSupportedOnHalfLine residual activation := by
  intro k t ht hbefore
  by_cases hk : k = 0
  · subst k
    have htneg : t < 0 := by
      simpa [activation] using hbefore
    exfalso
    linarith
  · simp [residual, hk]

/-- Every residual after the zeroth shell vanishes exactly. -/
theorem residual_tail_zero
    {k : ℕ}
    (hk : 1 ≤ k)
    (t : ℝ) :
    residual k t = 0 := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp [residual, hk0]

/-- Every nonempty finite partial sum of the residual family equals one. -/
theorem residual_partial_sum_eq_one
    (n : ℕ)
    (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), residual k t) = 1 := by
  induction n with
  | zero => simp [residual]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
      simp [residual, hne, ih]

/-- Elementary epsilon-delta definition of a zero left limit. -/
def LeftLimitZero (f : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, T - δ < t → t < T → |f t| < ε

/-- The constant-one function does not tend to zero from the left at `T = 1`. -/
theorem constant_one_not_leftLimitZero :
    ¬ LeftLimitZero (fun _t : ℝ => (1 : ℝ)) 1 := by
  intro h
  rcases h ((1 : ℝ) / 2) (by norm_num) with ⟨δ, hδ, hnear⟩
  have hbad := hnear (1 - δ / 2) (by linarith) (by linarith)
  norm_num at hbad

/-- Exact finite logical countermodel: future support and a zero large-index
residual tail coexist with partial sums that are identically one and therefore
fail terminal vanishing. -/
theorem future_support_zero_tail_not_terminal_zero :
    FutureSupportedOnHalfLine residual activation ∧
    (∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, residual k t = 0) ∧
    (∀ n : ℕ, ∀ t : ℝ,
      (∑ k ∈ Finset.range (n + 1), residual k t) = 1) ∧
    ¬ LeftLimitZero (fun _t : ℝ => (1 : ℝ)) 1 := by
  refine ⟨residual_future_supported, ?_, ?_, constant_one_not_leftLimitZero⟩
  · intro k hk t
    exact residual_tail_zero hk t
  · intro n t
    exact residual_partial_sum_eq_one n t

/-- A function is terminally absent when it is identically zero on some whole
left-neighborhood of the terminal time.  This is the support hypothesis used by
the older, correct diagonal residual theorem in the research bank. -/
def TerminallyAbsent (f : ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ τ : ℝ, τ < T ∧ ∀ t : ℝ, τ ≤ t → t < T → f t = 0

/-- Terminal disappearance is enough to kill every zeroth-order terminal jet. -/
theorem terminallyAbsent_leftLimitZero
    {f : ℝ → ℝ}
    {T : ℝ}
    (h : TerminallyAbsent f T) :
    LeftLimitZero f T := by
  intro ε hε
  rcases h with ⟨τ, hτ, hzero⟩
  refine ⟨T - τ, by linarith, ?_⟩
  intro t hnear ht
  have hτt : τ ≤ t := by linarith
  rw [hzero t hτt ht]
  simpa using hε

/-- Exact finite-prefix plus uniform-tail repair.  If every chosen finite prefix
has zero left limit, the remainder can be made uniformly small, and the total
splits as prefix plus remainder, then the total has zero left limit.

This theorem is the abstract epsilon/2 closure step needed after terminal
support has killed the fixed low-shell prefix.  It intentionally does not hide
an infinite-series theorem inside the statement. -/
theorem leftLimitZero_of_prefix_tail
    (total : ℝ → ℝ)
    (prefix tail : ℕ → ℝ → ℝ)
    (T : ℝ)
    (hdecomp : ∀ K t, total t = prefix K t + tail K t)
    (hprefix : ∀ K, LeftLimitZero (prefix K) T)
    (htail : ∀ ε : ℝ, 0 < ε →
      ∃ K : ℕ, ∀ t : ℝ, t < T → |tail K t| < ε) :
    LeftLimitZero total T := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases htail (ε / 2) hhalf with ⟨K, hK⟩
  rcases hprefix K (ε / 2) hhalf with ⟨δ, hδ, hpre⟩
  refine ⟨δ, hδ, ?_⟩
  intro t hnear ht
  have hp := hpre t hnear ht
  have hr := hK t ht
  calc
    |total t| = |prefix K t + tail K t| := by rw [hdecomp K t]
    _ ≤ |prefix K t| + |tail K t| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add hp hr
    _ = ε := by ring

#print axioms residual_future_supported
#print axioms residual_tail_zero
#print axioms residual_partial_sum_eq_one
#print axioms constant_one_not_leftLimitZero
#print axioms future_support_zero_tail_not_terminal_zero
#print axioms terminallyAbsent_leftLimitZero
#print axioms leftLimitZero_of_prefix_tail

end NSTerminalSupportCounterexample
