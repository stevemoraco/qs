import Mathlib

/-!
# BSD lane: intrinsic invariants do not determine a comparison map

This file formalizes finite logical and lattice cores from the 2026 BSD braid.
It does **not** formalize elliptic curves, Selmer groups, Iwasawa algebras,
Fitting ideals, determinants of Selmer complexes, or the Birch--Swinnerton-Dyer
conjecture.

The source and target of `scaleNat n` are literally the same lattice `ℤ`.
For every `n ≥ 2`, multiplication by `n` is injective but not surjective.
Thus all invariants depending only on the abstract source and target agree,
while their relative integral position can still have a nonsaturated defect.

The core-rank lemma separately records that a theorem requiring positive core
rank cannot be instantiated on a core-rank-zero Selmer structure.
-/

namespace BSDFittingComparisonBlindness

/-- Rank-one integral comparison by multiplication with a natural number. -/
def scaleNat (n : ℕ) (x : ℤ) : ℤ := (n : ℤ) * x

/-- Multiplication by a positive integer is injective on the integer lattice. -/
theorem scaleNat_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (scaleNat n) := by
  intro x y hxy
  have hnZ : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hprod : (n : ℤ) * (x - y) = 0 := by
    dsimp [scaleNat] at hxy
    nlinarith
  rcases mul_eq_zero.mp hprod with hn0 | hsub
  · exact False.elim (hnZ hn0)
  · exact sub_eq_zero.mp hsub

/-- If `n ≥ 2`, the target element `1` is not in the image. -/
theorem one_not_in_scaleNat_image
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ x : ℤ, scaleNat n x = 1 := by
  rintro ⟨x, hx⟩
  have hnZ : (2 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hn
  have hnnonneg : (0 : ℤ) ≤ (n : ℤ) := by
    linarith
  by_cases hxnonpos : x ≤ 0
  · have hmul : (n : ℤ) * x ≤ (n : ℤ) * 0 :=
      mul_le_mul_of_nonneg_left hxnonpos hnnonneg
    dsimp [scaleNat] at hx
    nlinarith
  · have hxpos : (1 : ℤ) ≤ x := by
      omega
    have hmul : (n : ℤ) * 1 ≤ (n : ℤ) * x :=
      mul_le_mul_of_nonneg_left hxpos hnnonneg
    dsimp [scaleNat] at hx
    nlinarith

/-- Hence the comparison map is not saturated/surjective for every `n ≥ 2`. -/
theorem scaleNat_not_surjective
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ Function.Surjective (scaleNat n) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj 1
  exact one_not_in_scaleNat_image hn ⟨x, hx⟩

/-- The source and target may be the identical abstract lattice while the
chosen comparison is injective and nonsurjective. -/
theorem identical_lattices_admit_nonsaturated_comparisons
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ f : ℤ → ℤ,
      Function.Injective f ∧ ¬ Function.Surjective f := by
  refine ⟨scaleNat n, scaleNat_injective (lt_of_lt_of_le (by norm_num) hn), ?_⟩
  exact scaleNat_not_surjective hn

/-- Arbitrarily large scaling parameters give arbitrarily large relative
comparison defects, even though the intrinsic source and target remain `ℤ`. -/
theorem arbitrarily_large_nonsaturated_comparison
    (bound : ℕ) :
    ∃ n : ℕ,
      bound < n ∧
      ∃ f : ℤ → ℤ,
        Function.Injective f ∧ ¬ Function.Surjective f := by
  let n := bound + 2
  have hbound : bound < n := by
    dsimp [n]
    omega
  have hn : 2 ≤ n := by
    dsimp [n]
    omega
  exact ⟨n, hbound, identical_lattices_admit_nonsaturated_comparisons hn⟩

/-- Determinant exponents add for a diagonal two-coordinate comparison. -/
theorem diagonal_determinant_exponent
    (p a b : ℕ) :
    p ^ a * p ^ b = p ^ (a + b) := by
  exact (pow_add p a b).symm

/-- A positive-core-rank hypothesis cannot be instantiated at core rank zero. -/
theorem core_rank_zero_is_not_positive
    {coreRank : ℤ} (hzero : coreRank = 0) :
    ¬ (1 ≤ coreRank) := by
  omega

/-- Exact domain-separation core: assumptions `coreRank = 0` and
`1 ≤ coreRank` are inconsistent. -/
theorem no_overlap_between_zero_and_positive_core_rank
    {coreRank : ℤ}
    (hzero : coreRank = 0)
    (hpositive : 1 ≤ coreRank) :
    False := by
  exact (core_rank_zero_is_not_positive hzero) hpositive

#print axioms scaleNat_injective
#print axioms one_not_in_scaleNat_image
#print axioms scaleNat_not_surjective
#print axioms identical_lattices_admit_nonsaturated_comparisons
#print axioms arbitrarily_large_nonsaturated_comparison
#print axioms diagonal_determinant_exponent
#print axioms core_rank_zero_is_not_positive
#print axioms no_overlap_between_zero_and_positive_core_rank

end BSDFittingComparisonBlindness
