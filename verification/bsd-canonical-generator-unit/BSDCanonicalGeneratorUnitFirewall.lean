import Mathlib

/-!
# BSD lane: one-place rank repair and generator-unit blindness

This file formalizes two finite logical cores from the corrected BSD braid.
It does **not** formalize Selmer complexes, Stark/Kolyvagin systems, p-adic
L-functions, determinant functors, or the Birch--Swinnerton-Dyer conjecture.

1. If a one-place relaxation raises core rank by exactly one, then a core-rank
   zero structure becomes core rank one. Current arithmetic prior art proves
   such a relaxation mechanism in specific Selmer settings; here we formalize
   only the integer rank bookkeeping.

2. Equality of principal generated submodules/ideals does not determine a
   distinguished generator. The generators `2` and `-2` generate the same
   subgroup of `ℤ` but are distinct. This is the finite shadow of the unit
   ambiguity left by an Iwasawa main conjecture stated as equality of ideals:
   an element-level zeta/determinant comparison needs extra information.
-/

namespace BSDCanonicalGeneratorUnitFirewall

/-- The additive subgroup of `ℤ` consisting of multiples of `a`, represented
as a set so that the generator ambiguity is completely elementary. -/
def multiples (a : ℤ) : Set ℤ := {z | ∃ k : ℤ, z = k * a}

/-- Multiplying a generator by the unit `-1` does not change its principal
multiple set. -/
theorem multiples_neg_eq (a : ℤ) : multiples a = multiples (-a) := by
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    ring
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    ring

/-- Explicit generator blindness: two distinct elements generate exactly the
same principal multiple set. -/
theorem same_principal_data_distinct_generators :
    multiples (2 : ℤ) = multiples (-2 : ℤ) ∧ (2 : ℤ) ≠ -2 := by
  constructor
  · exact multiples_neg_eq 2
  · norm_num

/-- Therefore principal-ideal/submodule data alone cannot logically determine
which distinguished generator was intended. -/
theorem principal_data_does_not_determine_generator :
    ∃ a b : ℤ, a ≠ b ∧ multiples a = multiples b := by
  refine ⟨2, -2, ?_, ?_⟩
  · norm_num
  · exact multiples_neg_eq 2

/-- Abstract core-rank bookkeeping for a one-place relaxation: starting at
rank zero and adding one local rank lands at rank one. -/
theorem one_place_relaxation_repairs_core_rank
    {coreRank relaxedCoreRank : ℤ}
    (hzero : coreRank = 0)
    (hrelax : relaxedCoreRank = coreRank + 1) :
    relaxedCoreRank = 1 := by
  omega

/-- The direct positive-core-rank theorem still cannot be instantiated before
relaxation: core rank zero itself is not positive. -/
theorem direct_positive_core_rank_still_blocked
    {coreRank : ℤ} (hzero : coreRank = 0) :
    ¬ 1 ≤ coreRank := by
  omega

#print axioms multiples_neg_eq
#print axioms same_principal_data_distinct_generators
#print axioms principal_data_does_not_determine_generator
#print axioms one_place_relaxation_repairs_core_rank
#print axioms direct_positive_core_rank_still_blocked

end BSDCanonicalGeneratorUnitFirewall
