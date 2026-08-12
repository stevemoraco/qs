import Mathlib

/-!
# Finite local-relation core for the generalized Thomas route

This file formalizes only the elementary linear-algebra firewall behind a
local vanishing-cycle relation criterion. It does not formalize admissible
normal functions, Picard--Lefschetz theory, the generalized Thomas theorem,
or the Hodge conjecture.

There are no user-declared axioms or proof placeholders.
-/

namespace HodgeThomasRelationCore

variable {𝕜 E V : Type*}
variable [Field 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup V] [Module 𝕜 V]

/-- A coefficient functional detects a relation for `Δ` exactly when the
kernel of `Δ` is not contained in the kernel of the functional. -/
theorem exists_detected_relation_iff_not_le_kernel
    (Δ : E →ₗ[𝕜] V) (ℓ : E →ₗ[𝕜] 𝕜) :
    (∃ x : E, Δ x = 0 ∧ ℓ x ≠ 0) ↔
      ¬ LinearMap.ker Δ ≤ LinearMap.ker ℓ := by
  constructor
  · rintro ⟨x, hxΔ, hxℓ⟩ hle
    have hxkerΔ : x ∈ LinearMap.ker Δ := by
      simpa [LinearMap.mem_ker] using hxΔ
    have hxkerℓ : x ∈ LinearMap.ker ℓ := hle hxkerΔ
    exact hxℓ (by simpa [LinearMap.mem_ker] using hxkerℓ)
  · intro hnot
    by_contra hno
    apply hnot
    intro x hxkerΔ
    have hxΔ : Δ x = 0 := by
      simpa [LinearMap.mem_ker] using hxkerΔ
    have hxℓ : ℓ x = 0 := by
      by_contra hxℓne
      exact hno ⟨x, hxΔ, hxℓne⟩
    simpa [LinearMap.mem_ker] using hxℓ

/-- If the vanishing-cycle synthesis map is injective, there is no nonzero
relation for any coefficient functional to detect. -/
theorem no_detected_relation_of_injective
    (Δ : E →ₗ[𝕜] V) (ℓ : E →ₗ[𝕜] 𝕜)
    (hΔ : Function.Injective Δ) :
    ¬ ∃ x : E, Δ x = 0 ∧ ℓ x ≠ 0 := by
  rintro ⟨x, hxΔ, hxℓ⟩
  have hx0 : x = 0 := by
    apply hΔ
    simpa using hxΔ
  subst x
  exact hxℓ (by simp)

/-- A detected relation witnesses strict kernel shrinkage after adjoining the
coefficient functional. This is the coordinate-free form of the rank-one
augmentation test. -/
theorem detected_relation_strictly_shrinks_kernel
    (Δ : E →ₗ[𝕜] V) (ℓ : E →ₗ[𝕜] 𝕜)
    (hdet : ∃ x : E, Δ x = 0 ∧ ℓ x ≠ 0) :
    LinearMap.ker Δ ⊓ LinearMap.ker ℓ < LinearMap.ker Δ := by
  have hle : LinearMap.ker Δ ⊓ LinearMap.ker ℓ ≤ LinearMap.ker Δ :=
    inf_le_left
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hkerle : LinearMap.ker Δ ≤ LinearMap.ker ℓ := by
    intro x hx
    have hxinf : x ∈ LinearMap.ker Δ ⊓ LinearMap.ker ℓ := by
      rw [heq]
      exact hx
    exact hxinf.2
  exact (exists_detected_relation_iff_not_le_kernel Δ ℓ).mp hdet hkerle

end HodgeThomasRelationCore
