import Mathlib

namespace B2Round54

def delayedFloor (N k : Nat) : Nat := if k < N then 1 else 0

theorem bsd_delayed_floor_boundary_values
    (N : Nat) (hN : 0 < N) :
    And (delayedFloor N (N - 1) = 1) (delayedFloor N N = 0) := by
  constructor
  · have hlt : N - 1 < N := by omega
    simp [delayedFloor, hlt]
  · simp [delayedFloor]

#print axioms bsd_delayed_floor_boundary_values

end B2Round54
