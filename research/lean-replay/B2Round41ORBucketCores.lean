import Mathlib

namespace B2Round41ORBucketCores

/-- If `t + 1` selected support coordinates occupy at most `t` buckets,
then two distinct selected coordinates collide.  This is the deterministic
pigeonhole core of the one-sided OR-bucket soundness proof. -/
theorem low_occupancy_forces_collision
    {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (support : Finset α)
    (bucket : α → β)
    (t : ℕ)
    (hsupport : support.card = t + 1)
    (hoccupied : (support.image bucket).card ≤ t) :
    ∃ x ∈ support, ∃ y ∈ support, x ≠ y ∧ bucket x = bucket y := by
  have hcard : (support.image bucket).card < support.card := by
    omega
  exact Finset.exists_ne_map_eq_of_card_image_lt hcard

/-- A decoder accepting only signatures with at most `t` occupied buckets
cannot accept `t + 1` selected coordinates unless their bucket map collides. -/
theorem acceptance_implies_collision
    {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (support : Finset α)
    (bucket : α → β)
    (t : ℕ)
    (hsupport : support.card = t + 1)
    (haccept : (support.image bucket).card ≤ t) :
    ∃ x ∈ support, ∃ y ∈ support, x ≠ y ∧ bucket x = bucket y :=
  low_occupancy_forces_collision support bucket t hsupport haccept

#print axioms low_occupancy_forces_collision
#print axioms acceptance_implies_collision

end B2Round41ORBucketCores
