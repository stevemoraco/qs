import Mathlib

/-!
# PNP shared-decoder localization firewall

This file formalizes only the additive folding identity and the one-sided
cross-slice conflict used in the round-41 hostile audit.  It does not formalize
Boolean circuits, circuit size, sparse languages, NP, or P versus NP.
-/

namespace MillenniumBraid
namespace B2Round41PNP

/-- Coordinatewise aggregation of a finite family of blocks.  Instantiating
`A` with `ZMod 2` gives coordinatewise XOR. -/
def aggregate
    {J I A : Type*} [Fintype J] [AddCommMonoid A]
    (blocks : J → I → A) : I → A :=
  fun i => ∑ j, blocks j i

/-- Embed one active block against the zero background. -/
def singleBlock
    {J I A : Type*} [DecidableEq J] [Zero A]
    (j : J) (x : I → A) : J → I → A :=
  fun q i => if q = j then x i else 0

/-- A zero-background one-block input survives coordinatewise aggregation
exactly. -/
theorem aggregate_singleBlock
    {J I A : Type*} [Fintype J] [DecidableEq J] [AddCommMonoid A]
    (j : J) (x : I → A) :
    aggregate (singleBlock j x) = x := by
  funext i
  simp [aggregate, singleBlock]

/-- A common decoder applied after the aggregator. -/
def folded
    {J I A : Type*} [Fintype J] [AddCommMonoid A]
    (decoder : (I → A) → Bool) (blocks : J → I → A) : Bool :=
  decoder (aggregate blocks)

/-- Every single-block restriction of the folded construction is the same
common decoder. -/
theorem folded_singleBlock
    {J I A : Type*} [Fintype J] [DecidableEq J] [AddCommMonoid A]
    (decoder : (I → A) → Bool) (j : J) (x : I → A) :
    folded decoder (singleBlock j x) = decoder x := by
  simp [folded, aggregate_singleBlock]

/-- Complement core associated to a positive slice. -/
def negativeCore {U : Type*} (T : Set U) : Set U := Tᶜ

/-- If a point is positive in one slice but absent from another, perfect
completeness for a common decoder forces a false positive in the second
slice's complement core. -/
theorem crossSliceWitnessForcesError
    {U : Type*}
    (Ti Tj : Set U) (decoder : U → Bool) (x : U)
    (hxi : x ∈ Ti) (hxj : x ∉ Tj)
    (perfect : ∀ y ∈ Ti, decoder y = true) :
    x ∈ negativeCore Tj ∧ decoder x = true := by
  constructor
  · simpa [negativeCore] using hxj
  · exact perfect x hxi

/-- The preceding conflict is pointwise for every member of a randomized
support family; averaging cannot repair it. -/
theorem everySupportDecoderForcedError
    {S U : Type*}
    (Ti Tj : Set U) (decoder : S → U → Bool) (x : U)
    (hxi : x ∈ Ti) (hxj : x ∉ Tj)
    (perfect : ∀ s y, y ∈ Ti → decoder s y = true) :
    ∀ s, x ∈ negativeCore Tj ∧ decoder s x = true := by
  intro s
  exact crossSliceWitnessForcesError Ti Tj (decoder s) x hxi hxj
    (fun y hy => perfect s y hy)

#print axioms aggregate_singleBlock
#print axioms folded_singleBlock
#print axioms crossSliceWitnessForcesError
#print axioms everySupportDecoderForcedError

end B2Round41PNP
end MillenniumBraid
