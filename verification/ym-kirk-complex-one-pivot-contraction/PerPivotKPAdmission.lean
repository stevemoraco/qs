import Mathlib

namespace Millennium.YangMills

/-!
# Per-pivot row to Kotecky--Preiss admission

Finite combinatorial bridge for the complex compact-denominator repair.

A polymer incompatible with a fixed polymer must overlap at at least one pivot.
Therefore a uniform per-pivot weighted polymer row controls the whole
incompatibility row by the size of the fixed polymer's pivot support.  This is
the elementary finite reduction behind the standard Kotecky--Preiss choice
`a(Gamma) = alpha * |U(Gamma)|`.

This file proves only the finite overlap double-counting inequality.  It does
not prove the Kirk complex activity row, the Kotecky--Preiss cluster expansion,
zero-freeness of the compact denominator, Theorem 6.43, OS reconstruction,
Yang--Mills mass gap, or a Clay theorem.
-/

open scoped BigOperators

/-- A nonnegative polymer weight that overlaps a fixed polymer is bounded by
summing the same weight once for every pivot in the fixed support that the
polymer contains. -/
theorem overlap_weight_le_pivot_sum
    {Γ P : Type*} [DecidableEq P]
    (support : Γ → Finset P) (w : Γ → ℝ)
    (γ γ0 : Γ)
    (hw : 0 ≤ w γ)
    (hoverlap : (support γ ∩ support γ0).Nonempty) :
    w γ ≤ ∑ p ∈ support γ0, if p ∈ support γ then w γ else 0 := by
  rcases hoverlap with ⟨p, hp⟩
  have hpγ : p ∈ support γ := (Finset.mem_inter.mp hp).1
  have hp0 : p ∈ support γ0 := (Finset.mem_inter.mp hp).2
  let f : P → ℝ := fun q => if q ∈ support γ then w γ else 0
  have hf : ∀ q ∈ support γ0, 0 ≤ f q := by
    intro q hq
    by_cases hmem : q ∈ support γ
    · simp [f, hmem, hw]
    · simp [f, hmem]
  have hsingle : f p ≤ ∑ q ∈ support γ0, f q :=
    Finset.single_le_sum hf hp0
  simpa [f, hpγ] using hsingle

/-- A uniform per-pivot row controls the total weight of polymers incompatible
with a fixed polymer by `|support gamma0| * pivotRow`. -/
theorem incompatible_sum_le_card_mul_pivot_row
    {Γ P : Type*} [DecidableEq Γ] [DecidableEq P]
    (polymers : Finset Γ)
    (support : Γ → Finset P)
    (w : Γ → ℝ)
    (γ0 : Γ)
    (pivotRow : ℝ)
    (hw : ∀ γ ∈ polymers, 0 ≤ w γ)
    (hrow : ∀ p ∈ support γ0,
      (∑ γ ∈ polymers, if p ∈ support γ then w γ else 0) ≤ pivotRow) :
    (∑ γ ∈ polymers.filter (fun γ => (support γ ∩ support γ0).Nonempty), w γ)
      ≤ ((support γ0).card : ℝ) * pivotRow := by
  let overlapSet := polymers.filter (fun γ => (support γ ∩ support γ0).Nonempty)
  let g : Γ → ℝ := fun γ => ∑ p ∈ support γ0, if p ∈ support γ then w γ else 0
  have hpoint : ∀ γ ∈ overlapSet, w γ ≤ g γ := by
    intro γ hγ
    have hmem := Finset.mem_filter.mp hγ
    exact overlap_weight_le_pivot_sum support w γ γ0 (hw γ hmem.1) hmem.2
  have hfirst : (∑ γ ∈ overlapSet, w γ) ≤ ∑ γ ∈ overlapSet, g γ := by
    exact Finset.sum_le_sum hpoint
  have hg_nonneg : ∀ γ ∈ polymers, 0 ≤ g γ := by
    intro γ hγ
    exact Finset.sum_nonneg (fun p hp => by
      by_cases hmem : p ∈ support γ
      · simp [g, hmem, hw γ hγ]
      · simp [g, hmem])
  have hsubset : overlapSet ⊆ polymers := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).1
  have hsecond : (∑ γ ∈ overlapSet, g γ) ≤ ∑ γ ∈ polymers, g γ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun γ hγ hnot => hg_nonneg γ hγ)
  have hswap : (∑ γ ∈ polymers, g γ) =
      ∑ p ∈ support γ0, ∑ γ ∈ polymers, if p ∈ support γ then w γ else 0 := by
    simp [g, Finset.sum_comm]
  have hthird :
      (∑ p ∈ support γ0, ∑ γ ∈ polymers, if p ∈ support γ then w γ else 0)
        ≤ ∑ p ∈ support γ0, pivotRow := by
    exact Finset.sum_le_sum hrow
  have hconst : (∑ p ∈ support γ0, pivotRow) =
      ((support γ0).card : ℝ) * pivotRow := by
    simp
  calc
    (∑ γ ∈ polymers.filter (fun γ => (support γ ∩ support γ0).Nonempty), w γ)
        = ∑ γ ∈ overlapSet, w γ := by rfl
    _ ≤ ∑ γ ∈ overlapSet, g γ := hfirst
    _ ≤ ∑ γ ∈ polymers, g γ := hsecond
    _ = ∑ p ∈ support γ0, ∑ γ ∈ polymers, if p ∈ support γ then w γ else 0 := hswap
    _ ≤ ∑ p ∈ support γ0, pivotRow := hthird
    _ = ((support γ0).card : ℝ) * pivotRow := hconst

/-- Standard KP scalar corollary: if the per-pivot exponentially weighted row
is at most `alpha`, then the incompatibility row is bounded by
`alpha * |support gamma0|`. -/
theorem per_pivot_row_implies_kp_size_bound
    {Γ P : Type*} [DecidableEq Γ] [DecidableEq P]
    (polymers : Finset Γ)
    (support : Γ → Finset P)
    (w : Γ → ℝ)
    (γ0 : Γ)
    (alpha : ℝ)
    (hw : ∀ γ ∈ polymers, 0 ≤ w γ)
    (hrow : ∀ p ∈ support γ0,
      (∑ γ ∈ polymers, if p ∈ support γ then w γ else 0) ≤ alpha) :
    (∑ γ ∈ polymers.filter (fun γ => (support γ ∩ support γ0).Nonempty), w γ)
      ≤ alpha * ((support γ0).card : ℝ) := by
  have h := incompatible_sum_le_card_mul_pivot_row
    polymers support w γ0 alpha hw hrow
  nlinarith

#print axioms overlap_weight_le_pivot_sum
#print axioms incompatible_sum_le_card_mul_pivot_row
#print axioms per_pivot_row_implies_kp_size_bound

end Millennium.YangMills
