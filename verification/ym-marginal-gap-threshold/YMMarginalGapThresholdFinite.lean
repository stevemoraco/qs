import Mathlib

/-!
# Yang--Mills marginal-running gap threshold: finite scalar core

Honesty status: this file formalizes only finite real-algebra consequences used
by the RG/gap compatibility note.  It does not formalize asymptotic freedom,
`exp (-c/g^2)`, lattice gauge theory, transfer operators, reflection positivity,
Osterwalder--Schrader reconstruction, the continuum limit, or the Clay
Yang--Mills statement.
-/

namespace MillenniumBraid
namespace YMMarginalGapThresholdFinite

theorem additiveGapTelescoping
    (m e : ℕ → ℝ)
    (hrec : ∀ n, m (n + 1) ≥ m n - e n) :
    ∀ N, m N ≥ m 0 - ∑ n ∈ Finset.range N, e n := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep := hrec N
      norm_num [Nat.add_comm] at hstep ⊢
      linarith

theorem finiteGeometricTailIdentity
    (q : ℝ) (J N : ℕ) :
    (1 - q) * (∑ i ∈ Finset.range N, q ^ (J + i))
      = q ^ J - q ^ (J + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      rw [show J + (N + 1) = (J + N) + 1 by omega, pow_succ]
      ring

theorem finiteGeometricTailBudget
    (K q : ℝ) (J N : ℕ)
    (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    K * (∑ i ∈ Finset.range N, q ^ (J + i))
      ≤ K * (q ^ J / (1 - q)) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hpow : 0 ≤ q ^ (J + N) := pow_nonneg hq0 _
  have hid := finiteGeometricTailIdentity q J N
  have hmul :
      (1 - q) * (∑ i ∈ Finset.range N, q ^ (J + i)) ≤ q ^ J := by
    rw [hid]
    linarith
  have hsum :
      (∑ i ∈ Finset.range N, q ^ (J + i)) ≤ q ^ J / (1 - q) := by
    apply (le_div_iff₀ hden).2
    simpa [mul_comm] using hmul
  exact mul_le_mul_of_nonneg_left hsum hK

theorem geometricBudgetDivergesLinearly
    (K q : ℝ) (N : ℕ)
    (hK : 0 ≤ K) (hq : 1 ≤ q) :
    (N : ℝ) * K ≤ ∑ i ∈ Finset.range N, K * q ^ i := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hpow : 1 ≤ q ^ N := by
        induction N with
        | zero => simp
        | succ n ihn =>
            rw [pow_succ]
            nlinarith
      have hterm : K ≤ K * q ^ N := by
        exact mul_le_mul_of_nonneg_left hpow hK
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith

def drainedGap (μ K : ℝ) (n : ℕ) : ℝ :=
  max 0 (μ - (n : ℝ) * K)

theorem drainedGapRecurrence
    (μ K : ℝ) (n : ℕ) (hK : 0 ≤ K) :
    drainedGap μ K (n + 1) ≥ drainedGap μ K n - K := by
  unfold drainedGap
  by_cases h : 0 ≤ μ - (n : ℝ) * K
  · rw [max_eq_right h]
    have hmax :
        μ - ((n + 1 : ℕ) : ℝ) * K
          ≤ max 0 (μ - ((n + 1 : ℕ) : ℝ) * K) :=
      le_max_right _ _
    push_cast at hmax ⊢
    linarith
  · have hneg : μ - (n : ℝ) * K ≤ 0 := le_of_not_ge h
    rw [max_eq_left hneg]
    have hmax :
        0 ≤ max 0 (μ - ((n + 1 : ℕ) : ℝ) * K) :=
      le_max_left _ _
    linarith

theorem drainedGapEventuallyZero
    (μ K : ℝ) (N : ℕ)
    (hbudget : μ ≤ (N : ℝ) * K) :
    drainedGap μ K N = 0 := by
  unfold drainedGap
  rw [max_eq_left]
  exact sub_nonpos.mpr hbudget

theorem couplingNormalizationProductInvariant
    (c β λ : ℝ) (hλ : λ ≠ 0) :
    (c * λ ^ 2) * (β / λ ^ 2) = c * β := by
  field_simp
  ring

#print axioms additiveGapTelescoping
#print axioms finiteGeometricTailIdentity
#print axioms finiteGeometricTailBudget
#print axioms geometricBudgetDivergesLinearly
#print axioms drainedGapRecurrence
#print axioms drainedGapEventuallyZero
#print axioms couplingNormalizationProductInvariant

end YMMarginalGapThresholdFinite
end MillenniumBraid
