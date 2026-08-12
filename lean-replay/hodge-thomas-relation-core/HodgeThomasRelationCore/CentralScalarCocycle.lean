import Mathlib

/-!
# Central-scalar vanishing of one-cocycles

This file formalizes an elementary sufficient condition for every additive
one-cocycle to be a coboundary. It is an abstract helper theorem. It does not
prove that the homological monodromy group of a hyperplane-section family
contains the required central scalar, and it does not prove the Hodge
conjecture.

There are no user-declared axioms or proof placeholders.
-/

namespace HodgeThomasRelationCore

/-- If a central group element acts on a module as a scalar `a ≠ 1`, every
additive one-cocycle is a coboundary. No compatibility axioms for `ρ` beyond
the displayed cocycle identity and linearity of each `ρ g` are used. -/
theorem cocycle_is_coboundary_of_central_scalar
    {𝕜 G V : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup V] [Module 𝕜 V]
    (ρ : G → V →ₗ[𝕜] V)
    (z : G → V)
    (hz : ∀ g h : G, z (g * h) = z g + ρ g (z h))
    (c : G) (a : 𝕜)
    (hcentral : ∀ g : G, c * g = g * c)
    (hscalar : ∀ x : V, ρ c x = a • x)
    (ha : a ≠ 1) :
    ∃ v : V, ∀ g : G, z g = ρ g v - v := by
  refine ⟨(a - 1)⁻¹ • z c, ?_⟩
  intro g
  have hcomm : z c + ρ c (z g) = z g + ρ g (z c) := by
    calc
      z c + ρ c (z g) = z (c * g) := (hz c g).symm
      _ = z (g * c) := by rw [hcentral g]
      _ = z g + ρ g (z c) := hz g c
  have hlin : (a - 1) • z g = ρ g (z c) - z c := by
    rw [hscalar] at hcomm
    linear_combination (norm := module) hcomm
  have hne : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hscaled := congrArg (fun x : V => (a - 1)⁻¹ • x) hlin
  simp only [smul_sub, smul_smul] at hscaled
  have hinv : (a - 1)⁻¹ * (a - 1) = 1 := inv_mul_cancel₀ hne
  rw [hinv, one_smul] at hscaled
  simpa only [map_smul] using hscaled

/-- In particular, over a field of characteristic different from two, a
central element acting by `-1` annihilates first cohomology in the standard
module. -/
theorem cocycle_is_coboundary_of_central_negation
    {𝕜 G V : Type*}
    [Field 𝕜] [NeZero (2 : 𝕜)] [Group G]
    [AddCommGroup V] [Module 𝕜 V]
    (ρ : G → V →ₗ[𝕜] V)
    (z : G → V)
    (hz : ∀ g h : G, z (g * h) = z g + ρ g (z h))
    (c : G)
    (hcentral : ∀ g : G, c * g = g * c)
    (hneg : ∀ x : V, ρ c x = -x) :
    ∃ v : V, ∀ g : G, z g = ρ g v - v := by
  apply cocycle_is_coboundary_of_central_scalar ρ z hz c (-1 : 𝕜) hcentral
  · intro x
    simpa using hneg x
  · intro h
    have htwo : (2 : 𝕜) = 0 := by
      calc
        (2 : 𝕜) = 1 + 1 := by norm_num
        _ = -1 + 1 := by rw [h]
        _ = 0 := neg_add_cancel 1
    exact (NeZero.ne (2 : 𝕜)) htwo

end HodgeThomasRelationCore
