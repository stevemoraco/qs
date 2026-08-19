import Mathlib

/-!
# Gram-factor support projection firewall

Finite real-algebra core for the positivity-safe replacement of the
Faizal--Shabir mixed-entry mask.  If a positive transfer has a Gram
factorization, selecting a subset of Gram *factors* gives a nonnegative
quadratic contribution and an exact keep/long partition.  This is distinct
from masking matrix entries by a pair relation, which need not preserve PSD.

The file deliberately does not formalize the source-specific Peter--Weyl
support map, the blocked/interacting Yang--Mills Gram factorization, the OS
vacuum normalization, AF/IR identification, or the continuum mass gap.
-/

namespace Millennium.YangMills.FaizalShabirGramFactorSupportProjection

open scoped BigOperators

/-- Any subset of Gram-factor squares contributes a nonnegative quadratic form. -/
theorem gram_factor_subset_nonneg
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (amplitude : ι → ℝ) :
    0 ≤ ∑ i ∈ S, (amplitude i) ^ 2 := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (amplitude i))

/-- A disjoint partition of factor labels gives an exact keep/long split. -/
theorem gram_factor_partition_exact
    {ι : Type*} [DecidableEq ι]
    (keep long : Finset ι)
    (hdisj : Disjoint keep long)
    (amplitude : ι → ℝ) :
    (∑ i ∈ keep ∪ long, (amplitude i) ^ 2) =
      (∑ i ∈ keep, (amplitude i) ^ 2) +
      (∑ i ∈ long, (amplitude i) ^ 2) := by
  rw [Finset.sum_union hdisj]

/-- Removing a subset of Gram factors can only decrease the unnormalized
quadratic form.  Any later vacuum/transfer normalization is a separate theorem. -/
theorem gram_keep_le_total
    {ι : Type*} [DecidableEq ι]
    (keep long : Finset ι)
    (hdisj : Disjoint keep long)
    (amplitude : ι → ℝ) :
    (∑ i ∈ keep, (amplitude i) ^ 2) ≤
      ∑ i ∈ keep ∪ long, (amplitude i) ^ 2 := by
  have hsplit := gram_factor_partition_exact keep long hdisj amplitude
  have hlong := gram_factor_subset_nonneg long amplitude
  linarith

#print axioms gram_factor_subset_nonneg
#print axioms gram_factor_partition_exact
#print axioms gram_keep_le_total

end Millennium.YangMills.FaizalShabirGramFactorSupportProjection
