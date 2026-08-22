import Mathlib

/-!
# P versus NP: finite encoder collision core

If a finite encoder has a larger domain than codomain, it is not injective.
Specializing the domain and codomain to finite function boxes yields the
finite pigeonhole core used in the short-integer-relation obstruction.

This file does not formalize exponent matrices, rational rank, pivot
coordinates, integer kernel vectors, the external 2026 paper, asymptotics,
arithmetic circuits, or `P != NP`.
-/

namespace PNP
namespace FiniteEncoderCollision

/-- A finite map from a larger type to a smaller type cannot be injective. -/
theorem not_injective_of_card_lt
    {Domain Codomain : Type*}
    [Fintype Domain] [Fintype Codomain]
    (encode : Domain → Codomain)
    (hcard : Fintype.card Codomain < Fintype.card Domain) :
    ¬ Function.Injective encode := by
  intro hinjective
  have hle : Fintype.card Domain ≤ Fintype.card Codomain :=
    Fintype.card_le_of_injective encode hinjective
  omega

/-- Hence two distinct domain points have the same encoded state. -/
theorem exists_collision_of_card_lt
    {Domain Codomain : Type*}
    [Fintype Domain] [Fintype Codomain]
    (encode : Domain → Codomain)
    (hcard : Fintype.card Codomain < Fintype.card Domain) :
    ∃ x y : Domain, x ≠ y ∧ encode x = encode y := by
  have hnot := not_injective_of_card_lt encode hcard
  simpa [Function.Injective] using hnot

/--
Function-box specialization: `(q+1)^m` coefficient states cannot inject into
`(R+1)^r` geometric states when the latter cardinality is smaller.
-/
theorem coefficient_box_encoder_not_injective
    (m r q R : ℕ)
    (encode : (Fin m → Fin (q + 1)) → (Fin r → Fin (R + 1)))
    (hcapacity : (R + 1) ^ r < (q + 1) ^ m) :
    ¬ Function.Injective encode := by
  apply not_injective_of_card_lt encode
  simpa using hcapacity

/-- Explicit collision form of the coefficient-box capacity theorem. -/
theorem exists_coefficient_box_collision
    (m r q R : ℕ)
    (encode : (Fin m → Fin (q + 1)) → (Fin r → Fin (R + 1)))
    (hcapacity : (R + 1) ^ r < (q + 1) ^ m) :
    ∃ c c' : Fin m → Fin (q + 1),
      c ≠ c' ∧ encode c = encode c' := by
  apply exists_collision_of_card_lt encode
  simpa using hcapacity

/-- Finite arithmetic endpoint for the row-state capacity imbalance. -/
theorem row_state_capacity_contradiction
    (m r q M : ℕ)
    (hnecessary : (q + 1) ^ m ≤ (q * m * M + 1) ^ r)
    (himbalance : (q * m * M + 1) ^ r < (q + 1) ^ m) :
    False := by
  omega

#print axioms not_injective_of_card_lt
#print axioms exists_collision_of_card_lt
#print axioms coefficient_box_encoder_not_injective
#print axioms exists_coefficient_box_collision
#print axioms row_state_capacity_contradiction

end FiniteEncoderCollision
end PNP
