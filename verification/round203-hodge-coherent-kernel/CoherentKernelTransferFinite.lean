import Mathlib

/-!
# Round 203 Hodge transfer finite cores

This file formalizes only abstract linear/subspace implications. It does not
formalize compact Kähler manifolds, coherent analytic sheaves, analytic GRR,
Hodge structures, algebraic cycles, or the Hodge conjecture.
-/

namespace Millennium
namespace Round203Hodge

/-- If a reverse transform sends every algebraic target class into the coherent-
Chern subspace, then recovering a non-coherent source class modulo that subspace
certifies that the target class is nonalgebraic. -/
theorem coherent_reverse_transform_detects_nonalgebraicity
    {𝕜 HX HP : Type*}
    [Field 𝕜]
    [AddCommGroup HX] [Module 𝕜 HX]
    [AddCommGroup HP] [Module 𝕜 HP]
    (coherentChern : Submodule 𝕜 HX)
    (algebraic : Set HP)
    (back : HP →ₗ[𝕜] HX)
    (hpreserve : ∀ beta ∈ algebraic, back beta ∈ coherentChern)
    (alpha delta : HX) (beta : HP) (c : 𝕜)
    (halpha : alpha ∉ coherentChern)
    (hdelta : delta ∈ coherentChern)
    (hc : c ≠ 0)
    (hrecover : back beta = c • alpha + delta) :
    beta ∉ algebraic := by
  intro hbeta
  have hback : back beta ∈ coherentChern := hpreserve beta hbeta
  have hscaled : c • alpha ∈ coherentChern := by
    have hsub : back beta - delta ∈ coherentChern :=
      coherentChern.sub_mem hback hdelta
    simpa [hrecover] using hsub
  have hunscaled : alpha ∈ coherentChern := by
    have hinv := coherentChern.smul_mem (c⁻¹) hscaled
    simpa [smul_smul, hc] using hinv
  exact halpha hunscaled

/-- In a subspace with nondegenerate restricted pairing, a nonzero vector
orthogonal to the whole subspace cannot belong to it. -/
theorem nonzero_orthogonal_class_is_not_algebraic
    {𝕜 V : Type*}
    [Zero 𝕜] [Zero V]
    (algebraic : Set V)
    (pairing : V → V → 𝕜)
    (hrestrictedNondegenerate :
      ∀ x ∈ algebraic, (∀ y ∈ algebraic, pairing x y = 0) → x = 0)
    (gamma : V)
    (hgamma : gamma ≠ 0)
    (horthogonal : ∀ y ∈ algebraic, pairing gamma y = 0) :
    gamma ∉ algebraic := by
  intro hmem
  exact hgamma (hrestrictedNondegenerate gamma hmem horthogonal)

/-- Failure of a vector-bundle resolution is only an existence statement; it
cannot by itself force a chosen characteristic-class detector to be nonzero. -/
theorem nonperfect_existence_does_not_force_detector
    {K : Type*} [Nonempty K]
    (nonperfect : K → Prop)
    (detector : K → ℚ)
    (hexists : ∃ k, nonperfect k) :
    (∃ k, nonperfect k) ∧
      ((detector = fun _ => 0) → ¬ ∃ k, detector k ≠ 0) := by
  constructor
  · exact hexists
  · intro hzero
    intro hnonzero
    rcases hnonzero with ⟨k, hk⟩
    exact hk (by rw [hzero])

#print axioms coherent_reverse_transform_detects_nonalgebraicity
#print axioms nonzero_orthogonal_class_is_not_algebraic
#print axioms nonperfect_existence_does_not_force_detector

end Round203Hodge
end Millennium
