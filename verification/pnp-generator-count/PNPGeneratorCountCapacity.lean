import Mathlib

open scoped BigOperators

/-!
# P versus NP: finite generator-count capacity core

A value obtained from `m` generators using at most `ell` copies of each
listed generator factors through the finite coefficient box
`Fin m → Fin (ell + 1)`.  Hence any represented value set has cardinality at
most `(ell + 1)^m`.

For repeated sums using at most `ell` summands in total, every multiplicity
coordinate is certainly at most `ell`, so the theorem supplies a coarse
finite generator-count cap.  The sharper stars-and-bars cap
`choose (m + ell) m - 1`, the proof that list sums admit multiplicity-vector
representations, rational row-rank reduction, the external 2026 paper,
asymptotics, arithmetic circuits, and `P != NP` are not formalized here.
-/

namespace PNP
namespace GeneratorCountCapacity

/-- Weighted evaluation of one bounded generator-multiplicity vector. -/
def coefficientEval {m : ℕ}
    (weights : Fin m → ℕ) (ell : ℕ)
    (c : Fin m → Fin (ell + 1)) : ℕ :=
  ∑ i, (c i : ℕ) * weights i

/-- All values obtainable from the bounded coefficient box. -/
def coefficientBoxValues {m : ℕ}
    (weights : Fin m → ℕ) (ell : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin m → Fin (ell + 1))).image
    (coefficientEval weights ell)

/-- The bounded generator-coefficient image cannot exceed its domain. -/
theorem coefficientBoxValues_card_le {m : ℕ}
    (weights : Fin m → ℕ) (ell : ℕ) :
    (coefficientBoxValues weights ell).card ≤ (ell + 1) ^ m := by
  unfold coefficientBoxValues
  calc
    ((Finset.univ : Finset (Fin m → Fin (ell + 1))).image
        (coefficientEval weights ell)).card
        ≤ (Finset.univ : Finset (Fin m → Fin (ell + 1))).card := by
          exact Finset.card_image_le
    _ = (ell + 1) ^ m := by
          simp

/-- Any finite set represented by bounded multiplicities obeys the cap. -/
theorem represented_values_card_le {m : ℕ}
    (weights : Fin m → ℕ) (ell : ℕ)
    (values : Finset ℕ)
    (hvalues : ∀ x ∈ values,
      ∃ c : Fin m → Fin (ell + 1),
        x = coefficientEval weights ell c) :
    values.card ≤ (ell + 1) ^ m := by
  have hsub : values ⊆ coefficientBoxValues weights ell := by
    intro x hx
    rcases hvalues x hx with ⟨c, rfl⟩
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
  exact (Finset.card_le_card hsub).trans
    (coefficientBoxValues_card_le weights ell)

/-- A represented value set strictly above generator-box capacity is impossible. -/
theorem no_represented_set_above_generator_capacity {m : ℕ}
    (weights : Fin m → ℕ) (ell : ℕ)
    (values : Finset ℕ)
    (hvalues : ∀ x ∈ values,
      ∃ c : Fin m → Fin (ell + 1),
        x = coefficientEval weights ell c)
    (hlarge : (ell + 1) ^ m < values.card) :
    False := by
  have hcap := represented_values_card_le weights ell values hvalues
  omega

/-- Finite arithmetic endpoint for the coarse Theorem-4 row budget. -/
theorem coarse_theorem4_row_budget_contradiction
    (n s : ℕ)
    (hnecessary : 8 * s ≤ 4 * n ^ 2)
    (hgap : n ^ 2 < 2 * s) :
    False := by
  omega

/-- Two simultaneous finite capacity bounds imply their minimum bound. -/
theorem card_le_min_of_two_bounds
    (cardinality rowCapacity stateCapacity : ℕ)
    (hrow : cardinality ≤ rowCapacity)
    (hstate : cardinality ≤ stateCapacity) :
    cardinality ≤ min rowCapacity stateCapacity := by
  exact le_min hrow hstate

#print axioms coefficientBoxValues_card_le
#print axioms represented_values_card_le
#print axioms no_represented_set_above_generator_capacity
#print axioms coarse_theorem4_row_budget_contradiction
#print axioms card_le_min_of_two_bounds

end GeneratorCountCapacity
end PNP
