import Mathlib

/-!
# Round 215 Hodge automorphic non-interior finite firewalls

This file formalizes only finite arithmetic and logical shadows used in the
hostile audit of arXiv:2602.06865.  It does **not** formalize orthogonal Shimura
varieties, Arthur parameters, automorphic representations, intersection
cohomology, Chow groups, the product-variety counterexample, or the Hodge
conjecture.
-/

namespace Millennium
namespace Round215Hodge

def typeIVRealDimension (n : ℕ) : ℕ := 2 * n

def typeIVComplexDimension (n : ℕ) : ℕ := n

theorem type_iv_2_26_real_dimension :
    typeIVRealDimension 26 = 52 := by
  norm_num [typeIVRealDimension]

theorem type_iv_2_26_complex_dimension :
    typeIVComplexDimension 26 = 26 := by
  rfl

theorem type_iv_2_26_not_complex_dimension_thirteen :
    typeIVComplexDimension 26 ≠ 13 := by
  norm_num [typeIVComplexDimension]

def specialOrthogonalDimension (n : ℕ) : ℕ := n * (n - 1) / 2

theorem so25_dimension : specialOrthogonalDimension 25 = 300 := by
  norm_num [specialOrthogonalDimension]

theorem adjoint_block_alone_dimension_mismatch : 3 * 1 ≠ 28 := by
  norm_num

theorem adjoint_plus_complement_dimension : 3 + 25 = 28 := by
  norm_num

def leftAction {U W : Type*} (g : U → U) : U × W → U × W :=
  fun x => (g x.1, x.2)

def rightAction {U W : Type*} (h : W → W) : U × W → U × W :=
  fun x => (x.1, h x.2)

theorem independent_summand_actions_commute
    {U W : Type*} (g : U → U) (h : W → W) (x : U × W) :
    leftAction g (rightAction h x) = rightAction h (leftAction g x) := by
  rfl

theorem nonzero_restriction_not_in_range
    {A B C : Type*} (f : A → B) (r : B → C) (z : B) (zero : C)
    (hzero : ∀ a, r (f a) = zero)
    (hz : r z ≠ zero) :
    z ∉ Set.range f := by
  intro h
  rcases h with ⟨a, rfl⟩
  exact hz (hzero a)

def compactSupportShadow (q : ℚ) : ℚ × ℚ := (q, 0)

def boundaryRestrictionShadow (x : ℚ × ℚ) : ℚ := x.2

theorem product_cycle_shadow_not_in_compact_support_image :
    ((0, 1) : ℚ × ℚ) ∉ Set.range compactSupportShadow := by
  apply nonzero_restriction_not_in_range
    compactSupportShadow boundaryRestrictionShadow ((0, 1) : ℚ × ℚ) 0
  · intro q
    rfl
  · norm_num [boundaryRestrictionShadow]

theorem universal_cycle_interior_conflicts_boundary
    {Cycle : Type*} (algebraic interior : Cycle → Prop) (z : Cycle)
    (hall : ∀ x, algebraic x → interior x)
    (halgebraic : algebraic z)
    (hnotInterior : ¬ interior z) :
    False := by
  exact hnotInterior (hall z halgebraic)

#print axioms type_iv_2_26_real_dimension
#print axioms type_iv_2_26_complex_dimension
#print axioms type_iv_2_26_not_complex_dimension_thirteen
#print axioms so25_dimension
#print axioms adjoint_block_alone_dimension_mismatch
#print axioms adjoint_plus_complement_dimension
#print axioms independent_summand_actions_commute
#print axioms nonzero_restriction_not_in_range
#print axioms product_cycle_shadow_not_in_compact_support_image
#print axioms universal_cycle_interior_conflicts_boundary

end Round215Hodge
end Millennium
