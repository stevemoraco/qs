import Mathlib

/-!
# Additive carrier embeddings in a fixed invariant fiber

The homogeneous Hessian construction has the abstract form

  `(x,y) ↦ carrier x y + g y`,

where a distinguished slice `x=x₀` annihilates the carrier. Restricting to that
slice recovers the arbitrary embedded object `g`. This file formalizes that
restriction and injectivity core independently of polynomial-derivative details.
-/

namespace PvsNP.AlgebraicFiberEmbedding

variable {R X Y : Type*} [AddMonoid R]

/-- Add an arbitrary `y`-function to a two-block carrier. -/
def additiveEmbed (carrier : X → Y → R) (g : Y → R) : X → Y → R :=
  fun x y => carrier x y + g y

/-- A zero-carrier slice recovers the embedded function exactly. -/
theorem recover_on_zero_carrier
    (carrier : X → Y → R) (g : Y → R) (x₀ : X)
    (hZero : ∀ y : Y, carrier x₀ y = 0) :
    ∀ y : Y, additiveEmbed carrier g x₀ y = g y := by
  intro y
  simp [additiveEmbed, hZero y]

/-- The additive carrier embedding is injective when a zero slice exists. -/
theorem additiveEmbed_injective
    (carrier : X → Y → R) (x₀ : X)
    (hZero : ∀ y : Y, carrier x₀ y = 0) :
    Function.Injective (additiveEmbed carrier) := by
  intro g h hEq
  funext y
  have hSlice := congrFun (congrFun hEq x₀) y
  simpa [additiveEmbed, hZero y] using hSlice

/-- Equality in the carrier family is equivalent to equality of embedded data. -/
theorem additiveEmbed_eq_iff
    (carrier : X → Y → R) (x₀ : X)
    (hZero : ∀ y : Y, carrier x₀ y = 0)
    (g h : Y → R) :
    additiveEmbed carrier g = additiveEmbed carrier h ↔ g = h := by
  constructor
  · exact additiveEmbed_injective carrier x₀ hZero
  · intro hgh
    simpa [hgh]

end PvsNP.AlgebraicFiberEmbedding
