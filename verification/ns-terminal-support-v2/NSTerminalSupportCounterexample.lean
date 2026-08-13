import Mathlib

namespace NSTerminalSupportCounterexample

noncomputable def activation (k : ℕ) : ℝ :=
  1 - ((1 : ℝ) / 2) ^ k

def residual (k : ℕ) (_t : ℝ) : ℝ :=
  if k = 0 then 1 else 0

def FutureSupportedOnHalfLine
    (E : ℕ → ℝ → ℝ)
    (t0 : ℕ → ℝ) : Prop :=
  ∀ k t, 0 ≤ t → t < t0 k → E k t = 0

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

theorem residual_tail_zero
    {k : ℕ}
    (hk : 1 ≤ k)
    (t : ℝ) :
    residual k t = 0 := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp [residual, hk0]

theorem residual_partial_sum_eq_one
    (n : ℕ)
    (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), residual k t) = 1 := by
  simp [residual]

def LeftLimitZero (f : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, T - δ < t → t < T → |f t| < ε

theorem constant_one_not_leftLimitZero :
    ¬ LeftLimitZero (fun _t : ℝ => (1 : ℝ)) 1 := by
  intro h
  rcases h ((1 : ℝ) / 2) (by norm_num) with ⟨δ, hδ, hnear⟩
  have hbad := hnear (1 - δ / 2) (by linarith) (by linarith)
  norm_num at hbad

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

def TerminallyAbsent (f : ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ τ : ℝ, τ < T ∧ ∀ t : ℝ, τ ≤ t → t < T → f t = 0

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

theorem leftLimitZero_of_finitePart_remainder
    (total : ℝ → ℝ)
    (finitePart remainder : ℕ → ℝ → ℝ)
    (T : ℝ)
    (hdecomp : ∀ K t, total t = finitePart K t + remainder K t)
    (hfinite : ∀ K, LeftLimitZero (finitePart K) T)
    (hremainder : ∀ ε : ℝ, 0 < ε →
      ∃ K : ℕ, ∀ t : ℝ, t < T → |remainder K t| < ε) :
    LeftLimitZero total T := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases hremainder (ε / 2) hhalf with ⟨K, hK⟩
  rcases hfinite K (ε / 2) hhalf with ⟨δ, hδ, hfiniteNear⟩
  refine ⟨δ, hδ, ?_⟩
  intro t hnear ht
  have hf := hfiniteNear t hnear ht
  have hr := hK t ht
  calc
    |total t| = |finitePart K t + remainder K t| := by rw [hdecomp K t]
    _ ≤ |finitePart K t| + |remainder K t| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add hf hr
    _ = ε := by ring

#print axioms residual_future_supported
#print axioms residual_tail_zero
#print axioms residual_partial_sum_eq_one
#print axioms constant_one_not_leftLimitZero
#print axioms future_support_zero_tail_not_terminal_zero
#print axioms terminallyAbsent_leftLimitZero
#print axioms leftLimitZero_of_finitePart_remainder

end NSTerminalSupportCounterexample
