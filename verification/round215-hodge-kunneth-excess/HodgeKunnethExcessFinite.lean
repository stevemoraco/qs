import Mathlib

/-!
# Round 215 Hodge Kunneth-excess finite cores

This file formalizes only abstract linear/submodule and quantifier facts. It
does not formalize complex manifolds, coherent analytic sheaves, perfect
complexes, K-theory, Grothendieck--Riemann--Roch, Kunneth decompositions, Hodge
structures, algebraic cycles, or the Hodge conjecture.
-/

namespace Millennium
namespace Round215Hodge

/-- If a linear map sends a spanning family into a submodule, then its entire
range lies in that submodule. This is the finite linear skeleton of the target-
spanning GRR no-go. -/
theorem spanning_tests_force_full_range
    {𝕜 X P : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup P] [Module 𝕜 P]
    (coherent : Submodule 𝕜 X)
    (back : P →ₗ[𝕜] X)
    (tests : Set P)
    (hspan : Submodule.span 𝕜 tests = ⊤)
    (htests : ∀ y ∈ tests, back y ∈ coherent) :
    LinearMap.range back ≤ coherent := by
  have hle : Submodule.span 𝕜 tests ≤ coherent.comap back := by
    apply Submodule.span_le.2
    intro y hy
    exact htests y hy
  intro x hx
  rcases hx with ⟨y, rfl⟩
  apply hle
  rw [hspan]
  exact Submodule.mem_top

/-- Once the full range lies in the coherent submodule, no target vector can
recover a source vector outside it. -/
theorem full_range_excludes_noncoherent_recovery
    {𝕜 X P : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup P] [Module 𝕜 P]
    (coherent : Submodule 𝕜 X)
    (back : P →ₗ[𝕜] X)
    (hrange : LinearMap.range back ≤ coherent)
    (beta : P)
    (houtside : back beta ∉ coherent) :
    False := by
  apply houtside
  exact hrange ⟨beta, rfl⟩

/-- The spanning-test theorem and the recovery firewall combine directly. -/
theorem spanning_tests_exclude_noncoherent_recovery
    {𝕜 X P : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup P] [Module 𝕜 P]
    (coherent : Submodule 𝕜 X)
    (back : P →ₗ[𝕜] X)
    (tests : Set P)
    (hspan : Submodule.span 𝕜 tests = ⊤)
    (htests : ∀ y ∈ tests, back y ∈ coherent)
    (beta : P)
    (houtside : back beta ∉ coherent) :
    False := by
  exact full_range_excludes_noncoherent_recovery coherent back
    (spanning_tests_force_full_range coherent back tests hspan htests)
    beta houtside

/-- Finite external-product-type linear combinations remain in the source
submodule whenever every source coefficient already lies there. -/
theorem finite_external_coefficients_stay_in_submodule
    {𝕜 X ι : Type*}
    [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [Fintype ι]
    (coherent : Submodule 𝕜 X)
    (x : ι → X)
    (a : ι → 𝕜)
    (hx : ∀ i, x i ∈ coherent) :
    ∑ i, a i • x i ∈ coherent := by
  apply Finset.sum_mem
  intro i hi
  exact coherent.smul_mem (a i) (hx i)

/-- A universal local property does not, by quantifier logic alone, force a
chosen global-resolution property. This is only a logical countermodel, not a
statement about complex manifolds. -/
theorem local_property_does_not_supply_global_resolution :
    ∃ (T : Type) (Local Global : T → Prop),
      (∀ t, Local t) ∧
      ¬ ∀ t, Global t := by
  refine ⟨Bool, (fun _ => True), (fun t => t = false), ?_⟩
  constructor
  · intro t
    trivial
  · intro hall
    have hbad := hall true
    simp at hbad

#print axioms spanning_tests_force_full_range
#print axioms full_range_excludes_noncoherent_recovery
#print axioms spanning_tests_exclude_noncoherent_recovery
#print axioms finite_external_coefficients_stay_in_submodule
#print axioms local_property_does_not_supply_global_resolution

end Round215Hodge
end Millennium
