import Mathlib

/-!
# Faizal--Shabir normalized reblocking-fiber firewall

Finite real-algebra firewall for arXiv:2606.19362v1, Lemma 10.2.

The printed proof bounds the reblocking fiber `X ↦ Y` by an unweighted finite
multiplicity `C_mult(b)` and then tries to beat the resulting prefactor by the
irrelevant factor `b^{-2}`.  For a coarse block containing a two-dimensional
`b × b` slice there are already `b^2` singleton fine placements projecting to
that same coarse block, so raw multiplicity alone can consume the full
`omega = 2` scaling gain.

The natural positive repair is not to count the fiber crudely: prove that the
actual reblocking coefficients form a uniformly normalized/Schur-summable row.
A convex row bound makes the estimate independent of the number of fine
preimages.  In the omega=2 case, a resulting fiber constant `C_fib` preserves
physical-time contraction exactly when `C_fib < b`.

This file formalizes only those finite scalar consumers.  It does not formalize
the Yang--Mills block map, polymer activities, FRD, the RG map, AF/IR
identification, OS reconstruction, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirNormalizedReblockingFiberFirewall

open scoped BigOperators

/-- A normalized nonnegative reblocking row controls a weighted fiber sum
without any cardinality factor. -/
theorem normalized_fiber_row_avoids_multiplicity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (weight value : ι → ℝ)
    (M : ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hvalue : ∀ i ∈ s, value i ≤ M)
    (hM : 0 ≤ M)
    (hrow : (∑ i ∈ s, weight i) ≤ 1) :
    (∑ i ∈ s, weight i * value i) ≤ M := by
  calc
    (∑ i ∈ s, weight i * value i)
        ≤ ∑ i ∈ s, weight i * M := by
          exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hvalue i hi) (hweight i hi)
    _ = (∑ i ∈ s, weight i) * M := by
          rw [Finset.sum_mul]
    _ ≤ 1 * M := by
          exact mul_le_mul_of_nonneg_right hrow hM
    _ = M := by ring

/-- In the four-dimensional Yang--Mills `omega = 2` ledger, a raw square
placement multiplicity exactly consumes the explicit `b^{-2}` scale gain. -/
theorem square_fiber_count_is_omega_two_critical
    (b : ℝ) (hb : b ≠ 0) :
    (b ^ 2) / (b ^ 2) = 1 := by
  exact div_self (pow_ne_zero 2 hb)

/-- A literal `1 / b^2` normalized average cancels `b^2` translational
placements exactly.  This is the finite shadow of the source's block-average
normalization; the actual polymer reblocking must prove that its coefficients
inherit an analogous normalized row. -/
theorem square_average_cancels_square_placement
    (b : ℝ) (hb : b ≠ 0) :
    (b ^ 2) * (1 / (b ^ 2)) = 1 := by
  field_simp [hb]

/-- If a repaired reblocking theorem yields one effective fiber constant
`C_fib`, then the omega=2 physical-time factor is `C_fib / b`. -/
theorem omega_two_physical_time_factor
    (Cfib b : ℝ) (hb : b ≠ 0) :
    (Cfib / (b ^ 2)) * b = Cfib / b := by
  field_simp [hb]

/-- Exact positive repair: a normalized reblocking-fiber constant strictly
smaller than the block factor gives physical-time contraction in the omega=2
case. -/
theorem normalized_fiber_constant_gives_physical_time_contraction
    (Cfib b : ℝ)
    (hb : 0 < b)
    (hC : Cfib < b) :
    (Cfib / (b ^ 2)) * b < 1 := by
  rw [omega_two_physical_time_factor Cfib b (ne_of_gt hb)]
  exact (div_lt_one hb).2 hC

/-- Uniform-row version: once the analytic reblocking row is bounded by a fixed
`C` and one chooses `C < b`, every smaller fiber constant is also admissible. -/
theorem bounded_normalized_fiber_constant_gives_physical_time_contraction
    (Cfib C b : ℝ)
    (hb : 0 < b)
    (hCfib : Cfib ≤ C)
    (hC : C < b) :
    (Cfib / (b ^ 2)) * b < 1 := by
  have hCfib_lt : Cfib < b := lt_of_le_of_lt hCfib hC
  exact normalized_fiber_constant_gives_physical_time_contraction Cfib b hb hCfib_lt

#print axioms normalized_fiber_row_avoids_multiplicity
#print axioms square_fiber_count_is_omega_two_critical
#print axioms square_average_cancels_square_placement
#print axioms omega_two_physical_time_factor
#print axioms normalized_fiber_constant_gives_physical_time_contraction
#print axioms bounded_normalized_fiber_constant_gives_physical_time_contraction

end Millennium.YangMills.FaizalShabirNormalizedReblockingFiberFirewall
