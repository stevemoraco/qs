import Mathlib

/-!
# Round 210 spinor-rank finite firewall

This file formalizes only finite rank arithmetic. It does not formalize spin
groups, spinor varieties, abelian varieties, derived categories, Chern
characters, Markman's theorem, or the Hodge conjecture.
-/

namespace Millennium
namespace Round210Hodge

/-- Even-cohomology rank of a complex abelian fourfold: half of `2^8`. -/
def abelianFourfoldEvenCohomologyRank : ℕ := 2 ^ 7

/-- Half-spin rank for a nondegenerate quadratic space of rank eight. -/
def rankEightHalfSpinRank : ℕ := 2 ^ (4 - 1)

/-- Half-spin rank for a nondegenerate quadratic space of rank sixteen. -/
def rankSixteenHalfSpinRank : ℕ := 2 ^ (8 - 1)

/-- Even-cohomology rank of a complex abelian surface: half of `2^4`. -/
def abelianSurfaceEvenCohomologyRank : ℕ := 2 ^ 3

theorem abelian_fourfold_even_rank_eq_128 :
    abelianFourfoldEvenCohomologyRank = 128 := by
  norm_num [abelianFourfoldEvenCohomologyRank]

theorem rank_eight_half_spin_eq_8 :
    rankEightHalfSpinRank = 8 := by
  norm_num [rankEightHalfSpinRank]

theorem rank_sixteen_half_spin_eq_128 :
    rankSixteenHalfSpinRank = 128 := by
  norm_num [rankSixteenHalfSpinRank]

theorem abelian_surface_even_rank_eq_8 :
    abelianSurfaceEvenCohomologyRank = 8 := by
  norm_num [abelianSurfaceEvenCohomologyRank]

/-- A rank-eight half-spin module cannot be the even cohomology of an abelian
fourfold. -/
theorem og48_module_not_fourfold_even_cohomology :
    rankEightHalfSpinRank ≠ abelianFourfoldEvenCohomologyRank := by
  norm_num [rankEightHalfSpinRank, abelianFourfoldEvenCohomologyRank]

/-- A rank-sixteen half-spin module has the correct scalar rank for the even
cohomology of an abelian fourfold. -/
theorem rank16_module_matches_fourfold_even_rank :
    rankSixteenHalfSpinRank = abelianFourfoldEvenCohomologyRank := by
  norm_num [rankSixteenHalfSpinRank, abelianFourfoldEvenCohomologyRank]

/-- The `OG(4,8)` rank-eight module instead matches the even cohomology rank of
an abelian surface, as in Markman's source setup. -/
theorem og48_module_matches_surface_even_rank :
    rankEightHalfSpinRank = abelianSurfaceEvenCohomologyRank := by
  norm_num [rankEightHalfSpinRank, abelianSurfaceEvenCohomologyRank]

#print axioms abelian_fourfold_even_rank_eq_128
#print axioms rank_eight_half_spin_eq_8
#print axioms rank_sixteen_half_spin_eq_128
#print axioms abelian_surface_even_rank_eq_8
#print axioms og48_module_not_fourfold_even_cohomology
#print axioms rank16_module_matches_fourfold_even_rank
#print axioms og48_module_matches_surface_even_rank

end Round210Hodge
end Millennium
