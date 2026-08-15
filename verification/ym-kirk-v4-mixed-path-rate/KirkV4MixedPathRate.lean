import Mathlib

/-!
# Mixed-path exponential rate assembly

Finite real-analysis bridge for the load-bearing final scalar step in Kirk v4
Theorem 6.43.  If every object on a root-to-root path pays at least one common
positive rate and the total reported path length dominates the root separation
up to a fixed endpoint constant, then the product exponential retains that
common rate, with only a fixed prefactor loss.

This file does not prove any Yang--Mills polymer estimate, BKAR forest theorem,
reported-hull geometry, continuum limit, Osterwalder--Schrader reconstruction,
mass gap, or Clay statement.
-/

namespace Millennium.YangMills

open scoped BigOperators

/-- If every path segment carries rate at least `m`, then the total paid
exponent dominates `m` times the total path length.  Combining this with a
reported-length lower bound gives the physical root-separation payment. -/
theorem mixed_path_rate_lower
    {ι : Type} [Fintype ι]
    (mu len : ι → ℝ) {m d C : ℝ}
    (hm : 0 ≤ m)
    (hlen : ∀ i, 0 ≤ len i)
    (hmu : ∀ i, m ≤ mu i)
    (hgeom : d - C ≤ ∑ i, len i) :
    m * (d - C) ≤ ∑ i, mu i * len i := by
  have hpoint : ∀ i, m * len i ≤ mu i * len i := by
    intro i
    exact mul_le_mul_of_nonneg_right (hmu i) (hlen i)
  have hsum : (∑ i, m * len i) ≤ ∑ i, mu i * len i := by
    exact Finset.sum_le_sum fun i hi => hpoint i
  have hgeom' : m * (d - C) ≤ m * (∑ i, len i) :=
    mul_le_mul_of_nonneg_left hgeom hm
  calc
    m * (d - C) ≤ m * (∑ i, len i) := hgeom'
    _ = ∑ i, m * len i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, mu i * len i := hsum

/-- Exponential form of `mixed_path_rate_lower`.  A fixed endpoint loss `C`
changes only the prefactor `exp(m C)` and does not weaken the surviving decay
rate `m` in the physical separation `d`. -/
theorem mixed_path_exp_bound
    {ι : Type} [Fintype ι]
    (mu len : ι → ℝ) {m d C : ℝ}
    (hm : 0 ≤ m)
    (hlen : ∀ i, 0 ≤ len i)
    (hmu : ∀ i, m ≤ mu i)
    (hgeom : d - C ≤ ∑ i, len i) :
    Real.exp (-(∑ i, mu i * len i)) ≤
      Real.exp (m * C) * Real.exp (-m * d) := by
  have hrate := mixed_path_rate_lower mu len hm hlen hmu hgeom
  have hneg : -(∑ i, mu i * len i) ≤ -(m * (d - C)) := by
    linarith
  have hexp : Real.exp (-(∑ i, mu i * len i)) ≤
      Real.exp (-(m * (d - C))) :=
    Real.exp_monotone hneg
  calc
    Real.exp (-(∑ i, mu i * len i))
        ≤ Real.exp (-(m * (d - C))) := hexp
    _ = Real.exp (m * C) * Real.exp (-m * d) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- With no endpoint defect, the mixed path keeps the full common rate with no
prefactor loss. -/
theorem mixed_path_exp_bound_zero_endpoint
    {ι : Type} [Fintype ι]
    (mu len : ι → ℝ) {m d : ℝ}
    (hm : 0 ≤ m)
    (hlen : ∀ i, 0 ≤ len i)
    (hmu : ∀ i, m ≤ mu i)
    (hgeom : d ≤ ∑ i, len i) :
    Real.exp (-(∑ i, mu i * len i)) ≤ Real.exp (-m * d) := by
  have hgeom0 : d - 0 ≤ ∑ i, len i := by
    simpa using hgeom
  simpa using
    (mixed_path_exp_bound mu len hm hlen hmu
      (C := 0) hgeom0)

#print axioms mixed_path_rate_lower
#print axioms mixed_path_exp_bound
#print axioms mixed_path_exp_bound_zero_endpoint

end Millennium.YangMills
