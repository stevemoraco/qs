import Mathlib

/-!
# Yang–Mills C465 — finite firewalls for gap debt, limit identification,
and observable-visible spectra

This file formalizes only elementary real/finite logic extracted from the human
source audit. It does not formalize gauge fields, transfer operators, RG,
Osterwalder–Schrader reconstruction, or Yang–Mills.

The declarations prove:

* recursive gap loss telescopes against the full cumulative debt;
* bounded/summable-style cumulative debt need not leave a positive reserve;
* an additive comparison inequality with zero debt need not make two objects
  converge together;
* one observable may see decay rate `m` while a hidden spectral sector has a
  strictly smaller positive energy `ε`.
-/

noncomputable section

namespace Millennium.YangMills.C465

/-- Exact finite telescoping of a one-step gap-loss inequality. -/
theorem gap_debt_telescopes
    (gap debt : ℕ → ℝ)
    (hstep : ∀ k, gap (k + 1) ≥ gap k - debt k) :
    ∀ n, gap n ≥ gap 0 - ∑ k ∈ Finset.range n, debt k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ]
      linarith

/-- A positive initial gap and finite cumulative debt leave a positive gap only
when the debt is strictly smaller than the initial reserve. -/
theorem positive_reserve_from_strict_budget
    (gap debt : ℕ → ℝ)
    (hstep : ∀ k, gap (k + 1) ≥ gap k - debt k)
    {δ : ℝ} (hbudget : ∀ n, ∑ k ∈ Finset.range n, debt k ≤ gap 0 - δ) :
    ∀ n, gap n ≥ δ := by
  intro n
  have ht := gap_debt_telescopes gap debt hstep n
  have hb := hbudget n
  linarith

/-- Countermodel: the initial gap is positive and every partial debt sum is
finite/bounded, but no positive uniform gap survives. -/
def budgetGap (n : ℕ) : ℝ := if n = 0 then 1 else 0

/-- One unit of debt is paid at the first step and zero thereafter. -/
def budgetDebt (n : ℕ) : ℝ := if n = 0 then 1 else 0

theorem finite_debt_no_positive_reserve :
    budgetGap 0 = 1 ∧
    (∀ n, 0 ≤ budgetGap n) ∧
    (∀ n, 0 ≤ budgetDebt n) ∧
    (∀ n, budgetGap (n + 1) ≥ budgetGap n - budgetDebt n) ∧
    (∀ n, ∑ k ∈ Finset.range n, budgetDebt k ≤ 1) ∧
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ n, δ ≤ budgetGap n := by
  constructor
  · simp [budgetGap]
  constructor
  · intro n
    simp [budgetGap]
  constructor
  · intro n
    simp [budgetDebt]
  constructor
  · intro n
    by_cases hn : n = 0
    · subst n
      norm_num [budgetGap, budgetDebt]
    · have hs : n + 1 ≠ 0 := Nat.succ_ne_zero n
      simp [budgetGap, budgetDebt, hn, hs]
  constructor
  · intro n
    cases n with
    | zero => simp
    | succ n =>
        rw [Finset.sum_range_succ]
        by_cases hn : n = 0
        · subst n
          norm_num [budgetDebt]
        · have hsum : ∑ k ∈ Finset.range n, budgetDebt k = 1 := by
            have hzero_mem : 0 ∈ Finset.range n := Finset.mem_range.mpr (Nat.pos_of_ne_zero hn)
            calc
              ∑ k ∈ Finset.range n, budgetDebt k
                  = ∑ k ∈ Finset.range n, if k = 0 then (1 : ℝ) else 0 := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      simp [budgetDebt]
              _ = 1 := by simp [hzero_mem]
          simp [budgetDebt, hn, hsum]
  · rintro ⟨δ, hδ, hall⟩
    have h := hall 1
    norm_num [budgetGap] at h
    linarith

/-- Constant nonzero mismatch with zero comparison debt. -/
def persistentMismatch (_ : ℕ) : ℝ := 1

def zeroComparisonDebt (_ : ℕ) : ℝ := 0

/-- An additive one-step comparison and even identically zero debt do not imply
that the mismatch tends to zero. -/
theorem additive_comparison_does_not_identify_limits :
    (∀ n,
      persistentMismatch (n + 1) ≤
        persistentMismatch n + zeroComparisonDebt n) ∧
    (∀ n, ∑ k ∈ Finset.range n, zeroComparisonDebt k = 0) ∧
    (∀ n, persistentMismatch n = 1) ∧
    ¬ ∃ N, ∀ n ≥ N, persistentMismatch n < (1 / 2 : ℝ) := by
  constructor
  · intro n
    norm_num [persistentMismatch, zeroComparisonDebt]
  constructor
  · intro n
    simp [zeroComparisonDebt]
  constructor
  · intro n
    rfl
  · rintro ⟨N, hN⟩
    have h := hN N le_rfl
    norm_num [persistentMismatch] at h

/-- A three-level spectral ledger: vacuum `0`, hidden low level `ε`, and the
level `m` seen by one selected observable. -/
structure ThreeLevelLedger where
  hiddenEnergy : ℝ
  visibleEnergy : ℝ
  hiddenPositive : 0 < hiddenEnergy
  hiddenBelowVisible : hiddenEnergy < visibleEnergy

/-- The selected observable correlation in the ledger. -/
noncomputable def ThreeLevelLedger.visibleCorrelation
    (L : ThreeLevelLedger) (t : ℝ) : ℝ :=
  Real.exp (-L.visibleEnergy * t)

/-- Exact hidden-sector countermodel: a visible correlation can decay at rate
`m` while the global first positive energy is any smaller `ε`. -/
theorem visible_decay_does_not_bound_hidden_gap
    {ε m : ℝ} (hε : 0 < ε) (hεm : ε < m) :
    ∃ L : ThreeLevelLedger,
      L.hiddenEnergy = ε ∧
      L.visibleEnergy = m ∧
      (∀ t, L.visibleCorrelation t = Real.exp (-m * t)) := by
  refine ⟨{
    hiddenEnergy := ε
    visibleEnergy := m
    hiddenPositive := hε
    hiddenBelowVisible := hεm
  }, rfl, rfl, ?_⟩
  intro t
  rfl

#print axioms gap_debt_telescopes
#print axioms positive_reserve_from_strict_budget
#print axioms finite_debt_no_positive_reserve
#print axioms additive_comparison_does_not_identify_limits
#print axioms visible_decay_does_not_bound_hidden_gap

end Millennium.YangMills.C465
