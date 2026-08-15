import Mathlib

/-!
# Navier--Stokes direction-persistence pigeonhole core

Finite combinatorial companion to the Type-I high-vorticity concurrency gate.

If finitely many persistent direction witnesses must be assigned to fewer
disjoint time slots than there are witnesses, then two witnesses share a slot.
The PDE application would require a separate theorem turning an interior
high-vorticity point into a uniform persistence interval and then discretizing
time into slots.  None of that PDE content is formalized here.
-/

namespace NSDirectionPersistencePigeonhole

/-- More witnesses than available time bins force two distinct witnesses into
the same bin. -/
theorem moreWitnessesThanBins_forceCollision
    {N K : ℕ} (hmore : K < N) (slot : Fin N → Fin K) :
    ∃ i j : Fin N, i ≠ j ∧ slot i = slot j := by
  by_contra hno
  push_neg at hno
  have hinj : Function.Injective slot := by
    intro i j hij
    by_contra hne
    exact hno i j hne hij
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (Fin K) :=
    Fintype.card_le_of_injective slot hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- The quantitative product floor used after a collision: two same-time sector
masses bounded below by `m` and separated by cost `d` pay at least `2 d m^2`.
This repeats the tiny scalar endgame locally so the pigeonhole core is reusable
without importing another research file. -/
def collisionDefectFloor (m d : ℝ) : ℝ := 2 * d * m ^ 2

theorem collisionDefectFloor_pos
    {m d : ℝ} (hm : 0 < m) (hd : 0 < d) :
    0 < collisionDefectFloor m d := by
  unfold collisionDefectFloor
  positivity

/-- If the actual same-time defect `A` dominates the collision floor, the
collision produces a strict positive defect. -/
theorem collisionFloor_transfers
    {A m d : ℝ}
    (hm : 0 < m) (hd : 0 < d)
    (hpay : collisionDefectFloor m d ≤ A) :
    0 < A := by
  exact lt_of_lt_of_le (collisionDefectFloor_pos hm hd) hpay

#print axioms moreWitnessesThanBins_forceCollision
#print axioms collisionDefectFloor_pos
#print axioms collisionFloor_transfers

end NSDirectionPersistencePigeonhole
