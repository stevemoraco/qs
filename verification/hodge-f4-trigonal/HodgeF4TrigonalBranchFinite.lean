import Mathlib

/-!
# F4 trigonal-branch finite core

Finite arithmetic and logic supporting the geometric obstruction to an
equivariant rational map between the F4 quotients in the first U-layer
`L^2 = 8` Hodge graph route.

This file does not formalize K3 surfaces, Hirzebruch surfaces, ramification,
Castelnuovo--Severi, or the Hodge conjecture.  Those remain explicit geometric
inputs in the companion research note.
-/

namespace HodgeF4TrigonalBranchFinite

/-- Intersection form on `F_4` in coordinates `a s + b f`, where
`s^2 = -4`, `s.f = 1`, and `f^2 = 0`. -/
def f4Intersection (a b c d : ℤ) : ℤ :=
  -4 * a * c + a * d + b * c

/-- The Weierstrass branch trisection `C = 3s + 12f` has fibre degree three. -/
theorem branch_trisection_fibre_degree :
    f4Intersection 3 12 0 1 = 3 := by
  norm_num [f4Intersection]

/-- The branch trisection is disjoint from the negative section. -/
theorem branch_trisection_negative_section_disjoint_numerically :
    f4Intersection 3 12 1 0 = 0 := by
  norm_num [f4Intersection]

/-- A target section in `|s + 4f|` has ruling degree one. -/
theorem target_section_fibre_degree :
    f4Intersection 1 4 0 1 = 1 := by
  norm_num [f4Intersection]

/-- A target section in `|s + 4f|` is disjoint from the negative section. -/
theorem target_section_negative_section_disjoint_numerically :
    f4Intersection 1 4 1 0 = 0 := by
  norm_num [f4Intersection]

/-- Self-intersection of the branch trisection. -/
theorem branch_trisection_self_intersection :
    f4Intersection 3 12 3 12 = 36 := by
  norm_num [f4Intersection]

/-- With `K_F4 = -2s - 6f`, the canonical degree on the branch trisection is -18. -/
theorem branch_trisection_canonical_intersection :
    f4Intersection 3 12 (-2) (-6) = -18 := by
  norm_num [f4Intersection]

/-- Numerical adjunction checkpoint: `(C^2 + K.C)/2 + 1 = 10`. -/
theorem branch_trisection_genus_ten_checkpoint :
    2 * (10 : ℤ) - 2 = 36 - 18 := by
  norm_num

/-- Castelnuovo--Severi's independent `(3,3)` bound is four, strictly below ten. -/
theorem independent_trigonal_genus_bound_is_too_small :
    (3 - 1 : ℤ) * (3 - 1) = 4 ∧ 4 < 10 := by
  norm_num

/-- If a common factor of two degree-three maps has degree > 1, its degree is
exactly three and both residual degrees are one. -/
theorem common_factor_of_two_degree_three_maps
    (e a b : ℕ)
    (he : 0 < e)
    (h₁ : e * a = 3)
    (h₂ : e * b = 3)
    (hne : e ≠ 1) :
    e = 3 ∧ a = 1 ∧ b = 1 := by
  omega

/-- The terminal set-theoretic collision: an injective degree-one fibre map
cannot identify two distinct branch points. -/
theorem injective_map_cannot_collapse_two_distinct_points
    {α β : Type*} (g : α → β) (x y : α)
    (hinj : Function.Injective g)
    (hxy : x ≠ y)
    (hcollapse : g x = g y) : False := by
  exact hxy (hinj hcollapse)

/-- Backup basepoint-budget firewall.  If a ruling-degree-one pencil has moving
class `s + b f`, then its square budget is `2b-4`.  If restriction to the
branch trisection has degree three while the raw intersection is `3b`, simple
branch centers demand at least `3b-3` units of multiplicity.  These inequalities
are incompatible with `b ≥ 2`. -/
theorem branch_basepoint_budget_impossible
    (b squareBudget branchMultiplicity : ℤ)
    (hb : 2 ≤ b)
    (hsquare : squareBudget = 2 * b - 4)
    (hbranch : branchMultiplicity = 3 * b - 3)
    (hdom : branchMultiplicity ≤ squareBudget) : False := by
  omega

#print axioms branch_trisection_fibre_degree
#print axioms branch_trisection_negative_section_disjoint_numerically
#print axioms target_section_fibre_degree
#print axioms target_section_negative_section_disjoint_numerically
#print axioms branch_trisection_self_intersection
#print axioms branch_trisection_canonical_intersection
#print axioms branch_trisection_genus_ten_checkpoint
#print axioms independent_trigonal_genus_bound_is_too_small
#print axioms common_factor_of_two_degree_three_maps
#print axioms injective_map_cannot_collapse_two_distinct_points
#print axioms branch_basepoint_budget_impossible

end HodgeF4TrigonalBranchFinite
