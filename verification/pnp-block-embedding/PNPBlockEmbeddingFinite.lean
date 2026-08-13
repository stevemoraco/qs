import Mathlib

/-!
# P versus NP: finite block-embedding sparsity core

This file formalizes only the finite cardinality spine of the block-embedded
local-hard-function candidate. It does not define Boolean circuits, affine
dispersers, P, NP, hardness magnification, asymptotics, or P versus NP.
-/

namespace MillenniumBraid
namespace PNPBlockEmbeddingFinite

/-- The image of all block/local-word pairs under an arbitrary embedding. -/
def embeddedSupport
    {J A X : Type*} [Fintype J] [Fintype A] [DecidableEq X]
    (encode : J × A → X) : Finset X :=
  Finset.univ.image encode

/-- Arbitrary collisions can only decrease the embedded support cardinality. -/
theorem card_embeddedSupport_le_product
    {J A X : Type*} [Fintype J] [Fintype A] [DecidableEq X]
    (encode : J × A → X) :
    (embeddedSupport encode).card ≤ Fintype.card J * Fintype.card A := by
  calc
    (embeddedSupport encode).card
        ≤ (Finset.univ : Finset (J × A)).card := by
          exact Finset.card_image_le
    _ = Fintype.card (J × A) := by simp
    _ = Fintype.card J * Fintype.card A := by simp

/-- For `m` blocks and all `r`-bit local words, the raw marker/support dictionary
has at most `m * 2^r` points. -/
theorem binary_block_support_le
    {X : Type*} [DecidableEq X]
    (m r : ℕ)
    (encode : Fin m × Fin (2 ^ r) → X) :
    (embeddedSupport encode).card ≤ m * 2 ^ r := by
  simpa using
    (card_embeddedSupport_le_product
      (J := Fin m) (A := Fin (2 ^ r)) encode)

/-- Exact cardinality of the abstract block/local-word description space. -/
theorem card_block_local_descriptions (m r : ℕ) :
    Fintype.card (Fin m × Fin (2 ^ r)) = m * 2 ^ r := by
  simp

/-- A subset of an embedded block dictionary inherits the same finite ceiling. -/
theorem subset_card_le_block_capacity
    {X : Type*} [DecidableEq X]
    (m r : ℕ)
    (encode : Fin m × Fin (2 ^ r) → X)
    (positive : Finset X)
    (hsub : positive ⊆ embeddedSupport encode) :
    positive.card ≤ m * 2 ^ r := by
  exact (Finset.card_le_card hsub).trans (binary_block_support_le m r encode)

#print axioms card_embeddedSupport_le_product
#print axioms binary_block_support_le
#print axioms card_block_local_descriptions
#print axioms subset_card_le_block_capacity

end PNPBlockEmbeddingFinite
end MillenniumBraid
