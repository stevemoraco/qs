import Mathlib

namespace NavierStokesRecurrentDepletionCocycle

/-- A fixed positive charge paid on each selected return interval telescopes
against a nonnegative budget.  This is the finite algebraic core of the
recurrent-orbit/depletion argument. -/
theorem finiteReturnDepletion
    (n : ℕ)
    (budget error : ℕ → ℝ)
    (c δ : ℝ)
    (hstep : ∀ k : ℕ,
      budget (k + 1) + c * δ ≤ budget k + error k)
    (hterminal : 0 ≤ budget n) :
    Finset.sum (Finset.range n) (fun _ => c * δ) ≤
      budget 0 + Finset.sum (Finset.range n) error := by
  have htel :
      budget n + Finset.sum (Finset.range n) (fun _ => c * δ) ≤
        budget 0 + Finset.sum (Finset.range n) error := by
    clear hterminal
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  linarith

/-- Infinitely many recurrence returns carrying one fixed positive charge are
incompatible with a nonnegative budget and a uniformly bounded cumulative
error.  No vanishing-threshold diagonal is needed once recurrence supplies a
fixed event floor. -/
theorem recurrentFixedChargeDepletionImpossible
    (budget error : ℕ → ℝ)
    (c δ E : ℝ)
    (hc : 0 < c)
    (hδ : 0 < δ)
    (hbudget : ∀ n : ℕ, 0 ≤ budget n)
    (hstep : ∀ k : ℕ,
      budget (k + 1) + c * δ ≤ budget k + error k)
    (herror : ∀ n : ℕ,
      Finset.sum (Finset.range n) error ≤ E) :
    False := by
  have hcharge : 0 < c * δ := mul_pos hc hδ
  obtain ⟨N, hN⟩ := exists_nat_gt ((budget 0 + E) / (c * δ))
  have hfinite :=
    finiteReturnDepletion N budget error c δ hstep (hbudget N)
  have herr := herror N
  have hsum :
      Finset.sum (Finset.range N) (fun _ => c * δ) =
        (N : ℝ) * (c * δ) := by
    simp
  have hover : budget 0 + E < (N : ℝ) * (c * δ) :=
    (div_lt_iff₀ hcharge).mp hN
  rw [hsum] at hfinite
  linarith

/-- Observable form of the same theorem.  If every sampled recurrent return
has activity at least `δ`, and activity is taxed with coefficient `c`, then a
bounded cumulative error cannot fund all returns. -/
theorem recurrentObservableDepletionImpossible
    (budget activity error : ℕ → ℝ)
    (c δ E : ℝ)
    (hc : 0 < c)
    (hδ : 0 < δ)
    (hbudget : ∀ n : ℕ, 0 ≤ budget n)
    (hactivity : ∀ n : ℕ, δ ≤ activity n)
    (hstep : ∀ k : ℕ,
      budget (k + 1) + c * activity k ≤ budget k + error k)
    (herror : ∀ n : ℕ,
      Finset.sum (Finset.range n) error ≤ E) :
    False := by
  have hstepFixed : ∀ k : ℕ,
      budget (k + 1) + c * δ ≤ budget k + error k := by
    intro k
    have hmul : c * δ ≤ c * activity k :=
      mul_le_mul_of_nonneg_left (hactivity k) (le_of_lt hc)
    linarith [hstep k]
  exact recurrentFixedChargeDepletionImpossible
    budget error c δ E hc hδ hbudget hstepFixed herror

/-- The bounded cumulative-error premise is load-bearing.  A unit error on
every return can fund perpetual unit activity while the budget stays zero. -/
theorem unitErrorFundsPerpetualUnitReturns :
    ∃ budget error : ℕ → ℝ,
      (∀ n : ℕ, 0 ≤ budget n) ∧
      (∀ n : ℕ, budget (n + 1) + 1 ≤ budget n + error n) ∧
      (∀ n : ℕ, error n = 1) := by
  refine ⟨(fun _ => 0), (fun _ => 1), ?_, ?_, ?_⟩
  · intro n
    norm_num
  · intro n
    norm_num
  · intro n
    rfl

#print axioms finiteReturnDepletion
#print axioms recurrentFixedChargeDepletionImpossible
#print axioms recurrentObservableDepletionImpossible
#print axioms unitErrorFundsPerpetualUnitReturns

end NavierStokesRecurrentDepletionCocycle
