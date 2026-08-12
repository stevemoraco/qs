import Mathlib

/-!
# Semiregularity-on-obstruction-image: finite linear-algebra core

Honesty status: this file formalizes only the logic of a factorization

    contraction = semiregularity ∘ obstruction

and its finite-dimensional rank consequence.

It does not formalize abelian varieties, coherent sheaves, Ext groups, Atiyah
classes, Hodge structures, algebraic cycles, Markman's construction, or the
Hodge Conjecture.
-/

namespace MillenniumBraid
namespace HodgeSemiregRank20

variable {K V E H : Type*}
variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup H] [Module K H]

/-- `sigma` is injective on the image of `ob`, written without introducing a
separate restricted linear map. -/
def InjectiveOnObstructionImage
    (ob : V →ₗ[K] E) (sigma : E →ₗ[K] H) : Prop :=
  ∀ x y : V, sigma (ob x) = sigma (ob y) → ob x = ob y

/-- The kernel of the obstruction map is always contained in the kernel of the
composite contraction map. -/
theorem ker_obstruction_le_ker_composite
    (ob : V →ₗ[K] E) (sigma : E →ₗ[K] H) :
    ob.ker ≤ (sigma.comp ob).ker := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  change sigma (ob x) = 0
  rw [hx, map_zero]

/-- Injectivity of semiregularity on the obstruction image is exactly equality
of the obstruction and contraction kernels. -/
theorem injectiveOnObstructionImage_iff_ker_eq
    (ob : V →ₗ[K] E) (sigma : E →ₗ[K] H) :
    InjectiveOnObstructionImage ob sigma ↔
      ob.ker = (sigma.comp ob).ker := by
  constructor
  · intro hinj
    apply le_antisymm (ker_obstruction_le_ker_composite ob sigma)
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply hinj x 0
    change sigma (ob x) = sigma (ob 0)
    simpa using hx
  · intro hker x y hxy
    have hcomp : x - y ∈ (sigma.comp ob).ker := by
      rw [LinearMap.mem_ker]
      simp only [LinearMap.comp_apply, map_sub]
      exact sub_eq_zero.mpr hxy
    have hob : x - y ∈ ob.ker := by
      rw [hker]
      exact hcomp
    rw [LinearMap.mem_ker] at hob
    apply sub_eq_zero.mp
    simpa only [map_sub] using hob

/-- Equal composite and obstruction ranks force equality of kernels because the
obstruction kernel is already contained in the composite kernel. -/
theorem ker_eq_of_finrank_range_eq
    [FiniteDimensional K V]
    (ob : V →ₗ[K] E) (sigma : E →ₗ[K] H)
    (hrank : Module.finrank K ob.range =
      Module.finrank K (sigma.comp ob).range) :
    ob.ker = (sigma.comp ob).ker := by
  apply Submodule.eq_of_le_of_finrank_eq
    (ker_obstruction_le_ker_composite ob sigma)
  have hob := LinearMap.finrank_range_add_finrank_ker ob
  have hcomp := LinearMap.finrank_range_add_finrank_ker (sigma.comp ob)
  omega

/-- In finite dimension, injectivity on the obstruction image is equivalent to
rank equality between the obstruction map and its semiregularity composite. -/
theorem injectiveOnObstructionImage_iff_finrank_range_eq
    [FiniteDimensional K V]
    (ob : V →ₗ[K] E) (sigma : E →ₗ[K] H) :
    InjectiveOnObstructionImage ob sigma ↔
      Module.finrank K ob.range =
        Module.finrank K (sigma.comp ob).range := by
  constructor
  · intro hinj
    have hker :=
      (injectiveOnObstructionImage_iff_ker_eq ob sigma).mp hinj
    have hkerFinrank :
        Module.finrank K ob.ker =
          Module.finrank K (sigma.comp ob).ker := by
      rw [hker]
    have hob := LinearMap.finrank_range_add_finrank_ker ob
    have hcomp := LinearMap.finrank_range_add_finrank_ker (sigma.comp ob)
    omega
  · intro hrank
    exact (injectiveOnObstructionImage_iff_ker_eq ob sigma).mpr
      (ker_eq_of_finrank_range_eq ob sigma hrank)

/-- Specialized finite statement used by the Markman reduction: once the
composite contraction rank is certified to be twenty, semiregularity is
injective on the obstruction image exactly when the obstruction rank is twenty.
The number twenty is data here, not a theorem about a geometric object. -/
theorem injectiveOnObstructionImage_iff_rank_eq_twenty
    [FiniteDimensional K V]
    (ob : V →ₗ[K] E) (sigma : E →ₗ[K] H)
    (hcomposite : Module.finrank K (sigma.comp ob).range = 20) :
    InjectiveOnObstructionImage ob sigma ↔
      Module.finrank K ob.range = 20 := by
  rw [injectiveOnObstructionImage_iff_finrank_range_eq, hcomposite]

#print axioms ker_obstruction_le_ker_composite
#print axioms injectiveOnObstructionImage_iff_ker_eq
#print axioms ker_eq_of_finrank_range_eq
#print axioms injectiveOnObstructionImage_iff_finrank_range_eq
#print axioms injectiveOnObstructionImage_iff_rank_eq_twenty

end HodgeSemiregRank20
end MillenniumBraid
