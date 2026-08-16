import Mathlib

namespace Millennium.YangMills

/-!
# Fixed-source-order versus common analytic-radius firewall

Finite logical firewall for a load-bearing continuum-source inference.
A theorem that, for every prescribed finite source order `n`, supplies some
regulator-uniform bound `C n` does not by itself control how `C n` grows with
`n`.  In particular it does not, without an additional growth theorem, produce
one regulator-uniform analytic source radius.

The diagonal family below realizes *any* prescribed nonnegative order-by-order
bound sequence exactly while retaining a uniform bound at every fixed order.
Thus fixed-order uniformity and uniform-in-order analyticity are distinct
quantifier statements.

This file does not formalize Kirk v4's source algebra, Schwinger functions,
Osterwalder--Schrader reconstruction, or Yang--Mills mass gap.
-/

/-- A regulator/order family that places the entire order-`n` coefficient at
regulator index `n`. -/
def diagonalSourceFamily (B : ℕ → ℝ) (reg order : ℕ) : ℝ :=
  if reg = order then B order else 0

/-- At each fixed source order, every regulator is bounded by the prescribed
order-dependent constant. -/
theorem diagonalSourceFamily_fixed_order_bound
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (reg order : ℕ) :
    |diagonalSourceFamily B reg order| ≤ B order := by
  unfold diagonalSourceFamily
  by_cases h : reg = order
  · rw [if_pos h, abs_of_nonneg (hB order)]
  · rw [if_neg h, abs_zero]
    exact hB order

/-- The order-dependent bound is attained exactly at the matching regulator
index. Hence the sequence of fixed-order constants may have arbitrary
nonnegative growth. -/
theorem diagonalSourceFamily_hits_bound (B : ℕ → ℝ) (order : ℕ) :
    diagonalSourceFamily B order order = B order := by
  simp [diagonalSourceFamily]

/-- Every prescribed nonnegative growth sequence is compatible with a family
that is regulator-uniform at each fixed source order and simultaneously attains
that growth order by order. This is the quantifier firewall used in the source
audit. -/
theorem fixed_order_uniformity_allows_arbitrary_order_growth
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) :
    (∀ order reg : ℕ, |diagonalSourceFamily B reg order| ≤ B order) ∧
      (∀ order : ℕ, diagonalSourceFamily B order order = B order) := by
  constructor
  · intro order reg
    exact diagonalSourceFamily_fixed_order_bound B hB reg order
  · exact diagonalSourceFamily_hits_bound B

/-- A finite collection of already-controlled source orders places no ceiling
on the next source order. -/
def nextOrderEscape (N : ℕ) (M : ℝ) (order : ℕ) : ℝ :=
  if order ≤ N then 0 else M + 1

theorem nextOrderEscape_controlled (N : ℕ) (M : ℝ) (order : ℕ)
    (h : order ≤ N) : nextOrderEscape N M order = 0 := by
  simp [nextOrderEscape, h]

theorem nextOrderEscape_next (N : ℕ) (M : ℝ) :
    nextOrderEscape N M (N + 1) = M + 1 := by
  simp [nextOrderEscape]

theorem nextOrderEscape_exceeds (N : ℕ) (M : ℝ) :
    M < nextOrderEscape N M (N + 1) := by
  rw [nextOrderEscape_next]
  linarith

#print axioms diagonalSourceFamily_fixed_order_bound
#print axioms diagonalSourceFamily_hits_bound
#print axioms fixed_order_uniformity_allows_arbitrary_order_growth
#print axioms nextOrderEscape_controlled
#print axioms nextOrderEscape_next
#print axioms nextOrderEscape_exceeds

end Millennium.YangMills
