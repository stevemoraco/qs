import Mathlib

namespace GrandTriad

theorem cancel
    {R : Type*} [CommRing R]
    (α β γ x y z : R) (h : α + β + γ = 0) :
    x * (α * y * z) + y * (β * z * x) + z * (γ * x * y) = 0 := by
  calc
    x * (α * y * z) + y * (β * z * x) + z * (γ * x * y) =
        (α + β + γ) * (x * y * z) := by ring
    _ = 0 := by rw [h]; ring

#print axioms cancel

end GrandTriad
