import Mathlib

namespace Millennium.YangMills

/-!
# Triangular source-product uniformity firewall

Finite algebra for a load-bearing continuum/RG quantifier check.

A uniformly bounded family of individual triangular maps does not imply a
uniform bound on products of arbitrarily many such maps.  The fixed unipotent
step below has a simple one-step `l1`-gauge bound, while repeated application
to `(0,1)` produces `(n,1)` and therefore has no depth-uniform bound.

This file proves only that finite-dimensional obstruction.  It does not
formalize Kirk's source-renormalization matrices, the Section 7-to-8 handoff,
Osterwalder--Schrader reconstruction, Yang--Mills, a mass gap, or a Clay
conclusion.
-/

/-- The unit upper-triangular step `(a,b) ↦ (a+b,b)`. -/
def unipotentStep (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 + x.2, x.2)

/-- A convenient `l1` gauge on the two-dimensional model. -/
def pairGauge (x : ℝ × ℝ) : ℝ :=
  |x.1| + |x.2|

/-- Every individual unipotent step has the same finite operator bound in the
chosen gauge. -/
theorem unipotentStep_pairGauge_le_two (x : ℝ × ℝ) :
    pairGauge (unipotentStep x) ≤ 2 * pairGauge x := by
  dsimp [pairGauge, unipotentStep]
  have hadd : |x.1 + x.2| ≤ |x.1| + |x.2| := abs_add x.1 x.2
  have h1 : 0 ≤ |x.1| := abs_nonneg x.1
  have h2 : 0 ≤ |x.2| := abs_nonneg x.2
  linarith

/-- The exact state obtained after `n` unit-triangular source steps on the
second basis vector. -/
def unipotentProductState (n : ℕ) : ℝ × ℝ :=
  ((n : ℝ), 1)

/-- The model states satisfy the exact triangular product recurrence. -/
theorem unipotentProductState_succ (n : ℕ) :
    unipotentProductState (n + 1) =
      unipotentStep (unipotentProductState n) := by
  ext <;> simp [unipotentProductState, unipotentStep]

/-- The depth-`n` product has gauge exactly `n+1`. -/
theorem unipotentProductState_pairGauge (n : ℕ) :
    pairGauge (unipotentProductState n) = (n : ℝ) + 1 := by
  simp [pairGauge, unipotentProductState, abs_of_nonneg]

/-- No real constant bounds all finite products, despite the uniform one-step
bound above. -/
theorem no_depth_uniform_bound_from_individual_triangular_bound (C : ℝ) :
    ∃ n : ℕ, C < pairGauge (unipotentProductState n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C - 1)
  refine ⟨n, ?_⟩
  rw [unipotentProductState_pairGauge]
  exact (sub_lt_iff_lt_add).mp hn

/-- A claimed product bound must be a genuinely stronger hypothesis than the
individual factor bound. -/
theorem individual_bound_does_not_supply_product_bound :
    (∀ x : ℝ × ℝ, pairGauge (unipotentStep x) ≤ 2 * pairGauge x) ∧
    (∀ C : ℝ, ∃ n : ℕ, C < pairGauge (unipotentProductState n)) := by
  exact ⟨unipotentStep_pairGauge_le_two,
    no_depth_uniform_bound_from_individual_triangular_bound⟩

#print axioms unipotentStep_pairGauge_le_two
#print axioms unipotentProductState_succ
#print axioms unipotentProductState_pairGauge
#print axioms no_depth_uniform_bound_from_individual_triangular_bound
#print axioms individual_bound_does_not_supply_product_bound

end Millennium.YangMills
