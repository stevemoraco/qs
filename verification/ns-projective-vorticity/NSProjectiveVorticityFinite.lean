import Mathlib

/-!
# Finite coordinate core for the projective-vorticity commutator repair

This file records only polynomial identities and scale arithmetic. It does not
formalize Riesz transforms, BMO, Lorentz spaces, Navier--Stokes, or the Clay
problem.
-/

namespace NSProjectiveVorticityFinite

/-- The first component of `x × ((x ⊗ x) v)` vanishes: a rank-one projection
onto `x` is parallel to `x`. -/
theorem rankOneParallelCross_first
    (x1 x2 x3 v1 v2 v3 : ℝ) :
    x2 * (x3 * (x1 * v1 + x2 * v2 + x3 * v3))
      - x3 * (x2 * (x1 * v1 + x2 * v2 + x3 * v3)) = 0 := by
  ring

/-- The second component of `x × ((x ⊗ x) v)` vanishes. -/
theorem rankOneParallelCross_second
    (x1 x2 x3 v1 v2 v3 : ℝ) :
    x3 * (x1 * (x1 * v1 + x2 * v2 + x3 * v3))
      - x1 * (x3 * (x1 * v1 + x2 * v2 + x3 * v3)) = 0 := by
  ring

/-- The third component of `x × ((x ⊗ x) v)` vanishes. -/
theorem rankOneParallelCross_third
    (x1 x2 x3 v1 v2 v3 : ℝ) :
    x1 * (x2 * (x1 * v1 + x2 * v2 + x3 * v3))
      - x2 * (x1 * (x1 * v1 + x2 * v2 + x3 * v3)) = 0 := by
  ring

/-- Removing an arbitrary component parallel to `x` leaves the first cross
contraction unchanged. This is the scalar coordinate shadow of replacing
`T omega` by `(I-P)T omega`. -/
theorem eraseParallel_first
    (x2 x3 v2 v3 dot : ℝ) :
    x2 * (v3 - x3 * dot) - x3 * (v2 - x2 * dot)
      = x2 * v3 - x3 * v2 := by
  ring

/-- Removing a parallel component leaves the second cross contraction
unchanged. -/
theorem eraseParallel_second
    (x1 x3 v1 v3 dot : ℝ) :
    x3 * (v1 - x1 * dot) - x1 * (v3 - x3 * dot)
      = x3 * v1 - x1 * v3 := by
  ring

/-- Removing a parallel component leaves the third cross contraction
unchanged. -/
theorem eraseParallel_third
    (x1 x2 v1 v2 dot : ℝ) :
    x1 * (v2 - x2 * dot) - x2 * (v1 - x1 * dot)
      = x1 * v2 - x2 * v1 := by
  ring

/-- A unit-vector rank-one projector fixes a collinear vector, first
coordinate. -/
theorem projectorFixesCollinear_first
    (x1 x2 x3 w : ℝ)
    (hunit : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1) :
    x1 * (x1 * (w * x1) + x2 * (w * x2) + x3 * (w * x3))
      = w * x1 := by
  calc
    x1 * (x1 * (w * x1) + x2 * (w * x2) + x3 * (w * x3))
        = w * x1 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) := by ring
    _ = w * x1 := by rw [hunit]; ring

/-- A unit-vector rank-one projector fixes a collinear vector, second
coordinate. -/
theorem projectorFixesCollinear_second
    (x1 x2 x3 w : ℝ)
    (hunit : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1) :
    x2 * (x1 * (w * x1) + x2 * (w * x2) + x3 * (w * x3))
      = w * x2 := by
  calc
    x2 * (x1 * (w * x1) + x2 * (w * x2) + x3 * (w * x3))
        = w * x2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) := by ring
    _ = w * x2 := by rw [hunit]; ring

/-- A unit-vector rank-one projector fixes a collinear vector, third
coordinate. -/
theorem projectorFixesCollinear_third
    (x1 x2 x3 w : ℝ)
    (hunit : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1) :
    x3 * (x1 * (w * x1) + x2 * (w * x2) + x3 * (w * x3))
      = w * x3 := by
  calc
    x3 * (x1 * (w * x1) + x2 * (w * x2) + x3 * (w * x3))
        = w * x3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) := by ring
    _ = w * x3 := by rw [hunit]; ring

/-- With amplitude `m^2` and slab width `m^-3`, the weak-`L^(3/2)` scale is
constant: amplitude times width to the `2/3` power has the algebraic factor
`m^2 * m^-2 = 1`. -/
theorem shearCriticalWeakScale
    (m : ℝ) (hm : 0 < m) :
    m ^ 2 * (1 / m ^ 2) = 1 := by
  field_simp [ne_of_gt hm]

/-- The squared velocity-energy scale of the shear is
`amplitude^2 * width^3 = m^-5`. -/
theorem shearEnergySquaredScale
    (m : ℝ) (hm : 0 < m) :
    (m ^ 2) ^ 2 * (1 / m ^ 3) ^ 3 = 1 / m ^ 5 := by
  field_simp [ne_of_gt hm]

/-- The slab width `m^-3` is far below the parabolic vorticity scale `m^-1`:
its squared width times vorticity amplitude is `m^-4`. -/
theorem shearSubcriticalWidthScale
    (m : ℝ) (hm : 0 < m) :
    (1 / m ^ 3) ^ 2 * m ^ 2 = 1 / m ^ 4 := by
  field_simp [ne_of_gt hm]

#print axioms rankOneParallelCross_first
#print axioms rankOneParallelCross_second
#print axioms rankOneParallelCross_third
#print axioms eraseParallel_first
#print axioms eraseParallel_second
#print axioms eraseParallel_third
#print axioms projectorFixesCollinear_first
#print axioms projectorFixesCollinear_second
#print axioms projectorFixesCollinear_third
#print axioms shearCriticalWeakScale
#print axioms shearEnergySquaredScale
#print axioms shearSubcriticalWidthScale

end NSProjectiveVorticityFinite
