import Mathlib

/-!
# Zero/one/two passive-root placement entropy

Finite real-algebra firewall for the passive-root bookkeeping omitted from the
printed proof of Kirk-v4 Theorem 5.27(U5).

The source-free connected-tree weight already pays all nonroot vertices. If a
finite source-order contribution has nonnegative weight `source`, and a tree has
at least one possible vertex `vertices`, then choosing zero or one passive root
costs no more than the common two-root envelope `source * vertices^2`.
More generally, any root-placement multiplier bounded by `vertices^2` is paid
by the same envelope.

This is the finite core behind the source repair: for fixed source order `N`,
the manuscript's own placement estimate at order `N + 2` pays `N` labelled
source leaves together with at most two passive exterior roots. It introduces
no new contraction threshold; it changes only a finite prefactor.

The last four declarations additionally separate root placement from root size:
if every fixed passive root has norm at most `M`, with `M >= 1`, then zero, one,
or two roots cost at most `M^2`, and this cost combines multiplicatively with
the quadratic placement envelope.

This file does not formalize replica--BKAR, Kirk's rooted Banach spaces, the
boundedness of the actual root atoms, weak RG, multiscale forests, continuum
Osterwalder--Schrader reconstruction, Yang--Mills theory, a mass gap, or a Clay
theorem.
-/

namespace Millennium.YangMills.BigradedRootPlacementEntropy

open scoped BigOperators

/-- One passive-root placement is bounded by the common two-root quadratic
envelope when the number of available vertices is at least one. -/
theorem one_root_placement_le_two_root_envelope
    (source vertices : ℝ)
    (hsource : 0 ≤ source)
    (hvertices : 1 ≤ vertices) :
    source * vertices ≤ source * vertices ^ 2 := by
  have hvertices_nonneg : 0 ≤ vertices := le_trans (by norm_num) hvertices
  have hsource_vertices_nonneg : 0 ≤ source * vertices :=
    mul_nonneg hsource hvertices_nonneg
  have hmul := mul_le_mul_of_nonneg_left hvertices hsource_vertices_nonneg
  simpa [pow_two, mul_assoc] using hmul

/-- Zero passive-root placements are also bounded by the common two-root
quadratic envelope. -/
theorem zero_root_placement_le_two_root_envelope
    (source vertices : ℝ)
    (hsource : 0 ≤ source)
    (hvertices : 1 ≤ vertices) :
    source ≤ source * vertices ^ 2 := by
  have hone : source ≤ source * vertices := by
    have hmul := mul_le_mul_of_nonneg_left hvertices hsource
    simpa using hmul
  exact hone.trans
    (one_root_placement_le_two_root_envelope source vertices hsource hvertices)

/-- Any placement multiplier for at most two roots is paid by the quadratic
vertex envelope. In the application, `source` already contains the fixed
source-leaf placement factor and the source-free tree weight. -/
theorem at_most_two_root_multiplier_le_quadratic_envelope
    (source vertices rootMultiplier : ℝ)
    (hsource : 0 ≤ source)
    (hroot : rootMultiplier ≤ vertices ^ 2) :
    source * rootMultiplier ≤ source * vertices ^ 2 := by
  exact mul_le_mul_of_nonneg_left hroot hsource

/-- Finite family version: the complete zero-root row is controlled by the
single two-root placement envelope. -/
theorem finite_zero_root_row_le_two_root_envelope
    {T : Type*} [DecidableEq T]
    (trees : Finset T)
    (source vertices : T → ℝ)
    (hsource : ∀ t ∈ trees, 0 ≤ source t)
    (hvertices : ∀ t ∈ trees, 1 ≤ vertices t) :
    (∑ t ∈ trees, source t) ≤
      ∑ t ∈ trees, source t * vertices t ^ 2 := by
  exact Finset.sum_le_sum fun t ht =>
    zero_root_placement_le_two_root_envelope
      (source t) (vertices t) (hsource t ht) (hvertices t ht)

/-- Finite family version: the complete one-root row is controlled by the
single two-root placement envelope. -/
theorem finite_one_root_row_le_two_root_envelope
    {T : Type*} [DecidableEq T]
    (trees : Finset T)
    (source vertices : T → ℝ)
    (hsource : ∀ t ∈ trees, 0 ≤ source t)
    (hvertices : ∀ t ∈ trees, 1 ≤ vertices t) :
    (∑ t ∈ trees, source t * vertices t) ≤
      ∑ t ∈ trees, source t * vertices t ^ 2 := by
  exact Finset.sum_le_sum fun t ht =>
    one_root_placement_le_two_root_envelope
      (source t) (vertices t) (hsource t ht) (hvertices t ht)

/-- Finite family version for an arbitrary placement multiplicity already
certified to be no larger than the two-root quadratic envelope. -/
theorem finite_at_most_two_root_placement_budget
    {T : Type*} [DecidableEq T]
    (trees : Finset T)
    (source vertices rootMultiplier : T → ℝ)
    (hsource : ∀ t ∈ trees, 0 ≤ source t)
    (hroot : ∀ t ∈ trees, rootMultiplier t ≤ vertices t ^ 2) :
    (∑ t ∈ trees, source t * rootMultiplier t) ≤
      ∑ t ∈ trees, source t * vertices t ^ 2 := by
  exact Finset.sum_le_sum fun t ht =>
    at_most_two_root_multiplier_le_quadratic_envelope
      (source t) (vertices t) (rootMultiplier t) (hsource t ht) (hroot t ht)

/-- If `M >= 1`, the empty-root norm factor is paid by the common two-root
norm envelope `M^2`. -/
theorem zero_root_atom_cost_le_uniform_square
    (M : ℝ)
    (hM : 1 ≤ M) :
    1 ≤ M ^ 2 := by
  have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM
  have hmul : (1 : ℝ) * 1 ≤ M * M :=
    mul_le_mul hM hM (by norm_num) hM_nonneg
  simpa [pow_two] using hmul

/-- One passive root of norm at most `M`, with `M >= 1`, is paid by the common
two-root norm envelope `M^2`. -/
theorem one_root_atom_cost_le_uniform_square
    (rootCost M : ℝ)
    (hroot : rootCost ≤ M)
    (hM : 1 ≤ M) :
    rootCost ≤ M ^ 2 := by
  have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM
  have hM_square : M ≤ M ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hM hM_nonneg
    simpa [pow_two] using hmul
  exact hroot.trans hM_square

/-- Two passive roots, each of norm at most `M`, cost at most `M^2`. -/
theorem two_root_atom_cost_le_uniform_square
    (rootCost₁ rootCost₂ M : ℝ)
    (hroot₂_nonneg : 0 ≤ rootCost₂)
    (hroot₁ : rootCost₁ ≤ M)
    (hroot₂ : rootCost₂ ≤ M)
    (hM_nonneg : 0 ≤ M) :
    rootCost₁ * rootCost₂ ≤ M ^ 2 := by
  have hmul : rootCost₁ * rootCost₂ ≤ M * M :=
    mul_le_mul hroot₁ hroot₂ hroot₂_nonneg hM_nonneg
  simpa [pow_two] using hmul

/-- The root-size square and the two-root placement square combine without
changing the source-free contraction threshold. -/
theorem combined_placement_and_root_cost
    (source vertices rootMultiplier rootCost M : ℝ)
    (hsource : 0 ≤ source)
    (hrootMultiplier : rootMultiplier ≤ vertices ^ 2)
    (hrootCost_nonneg : 0 ≤ rootCost)
    (hrootCost : rootCost ≤ M ^ 2) :
    source * rootMultiplier * rootCost ≤
      source * vertices ^ 2 * M ^ 2 := by
  have hplacement :
      source * rootMultiplier ≤ source * vertices ^ 2 :=
    mul_le_mul_of_nonneg_left hrootMultiplier hsource
  have hplacement_nonneg : 0 ≤ source * vertices ^ 2 :=
    mul_nonneg hsource (sq_nonneg vertices)
  exact mul_le_mul hplacement hrootCost hrootCost_nonneg hplacement_nonneg

#print axioms one_root_placement_le_two_root_envelope
#print axioms zero_root_placement_le_two_root_envelope
#print axioms at_most_two_root_multiplier_le_quadratic_envelope
#print axioms finite_zero_root_row_le_two_root_envelope
#print axioms finite_one_root_row_le_two_root_envelope
#print axioms finite_at_most_two_root_placement_budget
#print axioms zero_root_atom_cost_le_uniform_square
#print axioms one_root_atom_cost_le_uniform_square
#print axioms two_root_atom_cost_le_uniform_square
#print axioms combined_placement_and_root_cost

end Millennium.YangMills.BigradedRootPlacementEntropy
