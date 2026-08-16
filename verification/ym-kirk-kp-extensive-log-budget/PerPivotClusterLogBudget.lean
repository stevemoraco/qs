import Mathlib

namespace Millennium.YangMills

open scoped BigOperators

theorem cluster_weight_le_pivot_counted_sum
    {Γ P : Type*} [DecidableEq P]
    (pivots : Finset P)
    (support : Γ → Finset P)
    (w : Γ → ℝ)
    (γ : Γ)
    (hw : 0 ≤ w γ)
    (hnonempty : (support γ).Nonempty)
    (hsub : support γ ⊆ pivots) :
    w γ ≤ ∑ p ∈ pivots, if p ∈ support γ then w γ else 0 := by
  rcases hnonempty with ⟨p, hp⟩
  have hpp : p ∈ pivots := hsub hp
  let f : P → ℝ := fun q => if q ∈ support γ then w γ else 0
  have hf : ∀ q ∈ pivots, 0 ≤ f q := by
    intro q hq
    by_cases hmem : q ∈ support γ
    · simp [f, hmem, hw]
    · simp [f, hmem]
  have hsingle : f p ≤ ∑ q ∈ pivots, f q :=
    Finset.single_le_sum hf hpp
  simpa [f, hp] using hsingle

theorem per_pivot_cluster_row_implies_extensive_total
    {Γ P : Type*} [DecidableEq Γ] [DecidableEq P]
    (clusters : Finset Γ)
    (pivots : Finset P)
    (support : Γ → Finset P)
    (w : Γ → ℝ)
    (alpha : ℝ)
    (hw : ∀ γ ∈ clusters, 0 ≤ w γ)
    (hnonempty : ∀ γ ∈ clusters, (support γ).Nonempty)
    (hsub : ∀ γ ∈ clusters, support γ ⊆ pivots)
    (hrow : ∀ p ∈ pivots,
      (∑ γ ∈ clusters, if p ∈ support γ then w γ else 0) ≤ alpha) :
    (∑ γ ∈ clusters, w γ) ≤ ((pivots.card : ℕ) : ℝ) * alpha := by
  let g : Γ → ℝ := fun γ =>
    ∑ p ∈ pivots, if p ∈ support γ then w γ else 0
  have hpoint : ∀ γ ∈ clusters, w γ ≤ g γ := by
    intro γ hγ
    exact cluster_weight_le_pivot_counted_sum
      pivots support w γ (hw γ hγ) (hnonempty γ hγ) (hsub γ hγ)
  have hfirst : (∑ γ ∈ clusters, w γ) ≤ ∑ γ ∈ clusters, g γ := by
    exact Finset.sum_le_sum hpoint
  have hswap : (∑ γ ∈ clusters, g γ) =
      ∑ p ∈ pivots, ∑ γ ∈ clusters, if p ∈ support γ then w γ else 0 := by
    simp [g, Finset.sum_comm]
  have hthird :
      (∑ p ∈ pivots, ∑ γ ∈ clusters, if p ∈ support γ then w γ else 0)
        ≤ ∑ p ∈ pivots, alpha := by
    exact Finset.sum_le_sum hrow
  have hconst : (∑ p ∈ pivots, alpha) = ((pivots.card : ℕ) : ℝ) * alpha := by
    simp
  calc
    (∑ γ ∈ clusters, w γ) ≤ ∑ γ ∈ clusters, g γ := hfirst
    _ = ∑ p ∈ pivots, ∑ γ ∈ clusters, if p ∈ support γ then w γ else 0 := hswap
    _ ≤ ∑ p ∈ pivots, alpha := hthird
    _ = ((pivots.card : ℕ) : ℝ) * alpha := hconst

theorem per_pivot_cluster_row_bounds_absolute_log
    {Γ P : Type*} [DecidableEq Γ] [DecidableEq P]
    (clusters : Finset Γ)
    (pivots : Finset P)
    (support : Γ → Finset P)
    (w : Γ → ℝ)
    (alpha absLog : ℝ)
    (hw : ∀ γ ∈ clusters, 0 ≤ w γ)
    (hnonempty : ∀ γ ∈ clusters, (support γ).Nonempty)
    (hsub : ∀ γ ∈ clusters, support γ ⊆ pivots)
    (hrow : ∀ p ∈ pivots,
      (∑ γ ∈ clusters, if p ∈ support γ then w γ else 0) ≤ alpha)
    (hlog : absLog ≤ ∑ γ ∈ clusters, w γ) :
    absLog ≤ ((pivots.card : ℕ) : ℝ) * alpha := by
  exact le_trans hlog
    (per_pivot_cluster_row_implies_extensive_total
      clusters pivots support w alpha hw hnonempty hsub hrow)

theorem kp_cost_below_log_margin_preserves_contraction
    (theta alpha : ℝ)
    (htheta : 0 < theta)
    (hmargin : alpha < -Real.log theta) :
    theta * Real.exp alpha < 1 := by
  have hsum : Real.log theta + alpha < 0 := by
    linarith
  have hexp : Real.exp (Real.log theta + alpha) < Real.exp 0 :=
    Real.exp_lt_exp.mpr hsum
  have hthetaLog : Real.exp (Real.log theta) = theta :=
    Real.exp_log htheta
  calc
    theta * Real.exp alpha
        = Real.exp (Real.log theta) * Real.exp alpha := by rw [hthetaLog]
    _ = Real.exp (Real.log theta + alpha) := by rw [Real.exp_add]
    _ < Real.exp 0 := hexp
    _ = 1 := Real.exp_zero

#print axioms cluster_weight_le_pivot_counted_sum
#print axioms per_pivot_cluster_row_implies_extensive_total
#print axioms per_pivot_cluster_row_bounds_absolute_log
#print axioms kp_cost_below_log_margin_preserves_contraction

end Millennium.YangMills
