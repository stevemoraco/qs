import Mathlib

/-!
# Hodge lane: six-coordinate bivector-channel arithmetic

Fix the coordinate order
`(u∧v, u∧w, u∧z, v∧w, v∧z, w∧z)`.
At the level of coordinates, the expression

`a(v∧z) - b(v∧w) - c(u∧z) + d(u∧w)`

is represented by `(0,d,-c,-b,a,0)`. This file packages that assignment
as a linear map and proves that it has zero kernel.

This is a coordinate linear-algebra certificate. It does not construct an
exterior algebra, identify a geometric Atiyah-square map, prove a quotient
rank, or establish a Hodge-theoretic statement.
-/

namespace Millennium.Hodge.Phi2CoordinateInjectivity

noncomputable section

/-- The four coefficient channels placed in their six formal bivector
coordinates. -/
def phi2 (K : Type*) [CommRing K] :
    LinearMap (RingHom.id K) (Fin 4 → K) (Fin 6 → K) where
  toFun coeff :=
    ![0, coeff 3, -coeff 2, -coeff 1, coeff 0, 0]
  map_add' left right := by
    funext i
    fin_cases i <;> simp [add_comm]
  map_smul' scalar coeff := by
    funext i
    fin_cases i <;> simp

/-- Distinct coefficient inputs give distinct six-coordinate outputs. -/
theorem phi2_injective {K : Type*} [CommRing K] :
    Function.Injective (phi2 K) := by
  intro left right h
  funext i
  fin_cases i
  · simpa [phi2] using congrFun h (4 : Fin 6)
  · simpa [phi2] using congrFun h (3 : Fin 6)
  · simpa [phi2] using congrFun h (2 : Fin 6)
  · simpa [phi2] using congrFun h (1 : Fin 6)

/-- The coordinate vector vanishes exactly when all four coefficients
vanish. -/
theorem phi2_eq_zero_iff {K : Type*} [CommRing K]
    (coeff : Fin 4 → K) :
    phi2 K coeff = 0 ↔ coeff = 0 := by
  constructor
  · intro h
    apply phi2_injective
    simpa using h
  · intro h
    subst coeff
    exact LinearMap.map_zero (phi2 K)

/-- Any nonzero coefficient vector has a nonzero image. -/
theorem phi2_nonzero_of_nonzero {K : Type*} [CommRing K]
    {coeff : Fin 4 → K} (hcoeff : coeff ≠ 0) :
    phi2 K coeff ≠ 0 := by
  intro h
  exact hcoeff ((phi2_eq_zero_iff coeff).mp h)

#print axioms phi2_injective
#print axioms phi2_eq_zero_iff
#print axioms phi2_nonzero_of_nonzero

end

end Millennium.Hodge.Phi2CoordinateInjectivity
