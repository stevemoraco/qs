import Mathlib

/-!
# P versus NP: finite affine-slice capacity core

A family of at most `ell` slices, each encoded by an `a`-coordinate finite
state with side length `2 * ell * M + 1`, has at most

`ell * (2 * ell * M + 1)^a`

distinct outputs.  This is the finite image-cardinality core behind the
affine-rank sumset obstruction.

The file does not formalize affine dimension, pivot projections, the map from
row sums into signed coordinate boxes, the external 2026 paper, asymptotics,
arithmetic circuits, or `P != NP`.
-/

namespace PNP
namespace AffineSliceCapacity

/-- A scalar output encoded by a slice index and one bounded state vector. -/
def sliceStateEval {ell a M : ℕ}
    (encode : Fin ell → (Fin a → Fin (2 * ell * M + 1)) → ℕ)
    (state : Fin ell × (Fin a → Fin (2 * ell * M + 1))) : ℕ :=
  encode state.1 state.2

/-- All outputs of the finite slice-state encoder. -/
def sliceStateValues {ell a M : ℕ}
    (encode : Fin ell → (Fin a → Fin (2 * ell * M + 1)) → ℕ) :
    Finset ℕ :=
  (Finset.univ :
      Finset (Fin ell × (Fin a → Fin (2 * ell * M + 1)))).image
    (sliceStateEval encode)

/-- The image cannot exceed the product slice-state domain. -/
theorem sliceStateValues_card_le {ell a M : ℕ}
    (encode : Fin ell → (Fin a → Fin (2 * ell * M + 1)) → ℕ) :
    (sliceStateValues encode).card ≤
      ell * (2 * ell * M + 1) ^ a := by
  unfold sliceStateValues
  calc
    ((Finset.univ :
        Finset (Fin ell × (Fin a → Fin (2 * ell * M + 1)))).image
      (sliceStateEval encode)).card
      ≤ (Finset.univ :
          Finset (Fin ell × (Fin a → Fin (2 * ell * M + 1)))).card := by
            exact Finset.card_image_le
    _ = ell * (2 * ell * M + 1) ^ a := by
          simp

/-- Any finite output set represented by the slice-state encoder obeys the cap. -/
theorem represented_slice_values_card_le {ell a M : ℕ}
    (encode : Fin ell → (Fin a → Fin (2 * ell * M + 1)) → ℕ)
    (values : Finset ℕ)
    (hvalues : ∀ x ∈ values,
      ∃ state : Fin ell × (Fin a → Fin (2 * ell * M + 1)),
        x = sliceStateEval encode state) :
    values.card ≤ ell * (2 * ell * M + 1) ^ a := by
  have hsub : values ⊆ sliceStateValues encode := by
    intro x hx
    rcases hvalues x hx with ⟨state, rfl⟩
    exact Finset.mem_image.mpr
      ⟨state, Finset.mem_univ state, rfl⟩
  exact (Finset.card_le_card hsub).trans
    (sliceStateValues_card_le encode)

/-- A represented output set above affine-slice capacity is impossible. -/
theorem no_represented_set_above_affine_slice_capacity {ell a M : ℕ}
    (encode : Fin ell → (Fin a → Fin (2 * ell * M + 1)) → ℕ)
    (values : Finset ℕ)
    (hvalues : ∀ x ∈ values,
      ∃ state : Fin ell × (Fin a → Fin (2 * ell * M + 1)),
        x = sliceStateEval encode state)
    (hlarge : ell * (2 * ell * M + 1) ^ a < values.card) :
    False := by
  have hcap := represented_slice_values_card_le encode values hvalues
  omega

/-- Finite arithmetic endpoint for the coarse affine-rank source budget. -/
theorem coarse_affine_rank_budget_contradiction
    (s K a : ℕ)
    (hnecessary : 8 * s ≤ 3 + (K + 5) * a)
    (hgap : 3 + (K + 5) * a < 8 * s) :
    False := by
  omega

#print axioms sliceStateValues_card_le
#print axioms represented_slice_values_card_le
#print axioms no_represented_set_above_affine_slice_capacity
#print axioms coarse_affine_rank_budget_contradiction

end AffineSliceCapacity
end PNP
