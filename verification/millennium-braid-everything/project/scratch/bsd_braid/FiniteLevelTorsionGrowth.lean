import Mathlib

/-!
# BSD finite algebra: finite-level torsion growth

This file formalizes the pointwise and finite-sum identities behind
`FINITE_LEVEL_TORSION_GROWTH_AND_BOCKSTEIN_PREFIX_AREA_2026-08-11.md`.
It does not prove BSD.

For an elementary divisor of length `d`, its contribution at level `k` is
`min k d`.  Increasing the level from `k` to `k+1` adds exactly one if and
only if the divisor survives beyond depth `k`.
-/

namespace BSDProof
namespace FiniteLevelGrowth

/-- A single elementary divisor contributes one new unit of length at the
    next finite level exactly when it survives past the current level. -/
theorem min_succ_decomposition (k d : ℕ) :
    min (k + 1) d = min k d + if k < d then 1 else 0 := by
  by_cases h : k < d
  · have hk : k ≤ d := Nat.le_of_lt h
    have hks : k + 1 ≤ d := Nat.succ_le_iff.mpr h
    simp [Nat.min_eq_left hk, Nat.min_eq_left hks, h]
  · have hd : d ≤ k := Nat.le_of_not_gt h
    have hds : d ≤ k + 1 := le_trans hd (Nat.le_add_right k 1)
    simp [Nat.min_eq_right hd, Nat.min_eq_right hds, h]

/-- Corrected finite-level torsion growth for a finite family of elementary
    divisors. -/
def growth {ι : Type*} (s : Finset ι) (d : ι → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ s, min k (d i)

/-- The first difference of finite-level growth is the number of elementary
    divisors whose depth is strictly greater than the current level. -/
theorem growth_succ
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℕ) (k : ℕ) :
    growth s d (k + 1) =
      growth s d k + (s.filter fun i => k < d i).card := by
  unfold growth
  simp_rw [min_succ_decomposition]
  rw [Finset.sum_add_distrib]
  simp

end FiniteLevelGrowth
end BSDProof
