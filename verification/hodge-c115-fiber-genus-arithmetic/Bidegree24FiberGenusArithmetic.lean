import Mathlib

/-!
# Hodge C115 fibre-genus arithmetic shadow

This file formalizes only the integer arithmetic used after the geometric
Stein-factor, adjunction, and finite-birational genus theorems have supplied the
C114 source and image genus formulas. It does not formalize K3 surfaces,
finite covers, Stein factorization, arithmetic genus, or the Hodge conjecture.
-/

namespace Millennium.Hodge.Bidegree24FiberGenusArithmetic

/-- Arithmetic genus of the general elliptic pullback in the C114 family. -/
def sourceGenus (r : ℤ) : ℤ := 4 * r ^ 2 + 2 * r

/-- Arithmetic genus of its primitive finite-birational image on the K3. -/
def imageGenus (r : ℤ) : ℤ := 4 * r + 3

/-- The image class `(4r+1)e+h` has square `8r+4` in the Gram form
`2xy+2y^2`. -/
theorem image_class_square_identity (r : ℤ) :
    2 * (4 * r + 1) * 1 + 2 * 1 ^ 2 = 8 * r + 4 := by
  ring

/-- Exact genus-gap polynomial. -/
theorem genus_gap_identity (r : ℤ) :
    sourceGenus r - imageGenus r = 4 * r ^ 2 - 2 * r - 3 := by
  simp [sourceGenus, imageGenus]
  ring

/-- Every integral family parameter at least two gives a strict genus
contradiction. -/
theorem source_genus_gt_image_genus_of_two_le
    (r : ℤ) (hr : 2 ≤ r) :
    imageGenus r < sourceGenus r := by
  have hsquare : 0 ≤ (r - 2) ^ 2 := sq_nonneg (r - 2)
  simp [sourceGenus, imageGenus]
  nlinarith

/-- Finite-birational genus monotonicity therefore excludes every C114 row
with parameter at least two. -/
theorem genus_monotonicity_excludes_two_le
    (r : ℤ) (hr : 2 ≤ r)
    (hmono : sourceGenus r ≤ imageGenus r) :
    False := by
  exact (not_lt_of_ge hmono) (source_genus_gt_image_genus_of_two_le r hr)

/-- If a positive integral parameter survives the genus monotonicity test, it
must be the residual value one. -/
theorem genus_monotonicity_forces_parameter_one
    (r : ℤ) (hr : 1 ≤ r)
    (hmono : sourceGenus r ≤ imageGenus r) :
    r = 1 := by
  have hnot : ¬ 2 ≤ r := by
    intro hr2
    exact genus_monotonicity_excludes_two_le r hr2 hmono
  omega

/-- The fibre-image coordinate pair `(4r+1,1)` is primitive. -/
theorem fiber_image_coordinates_coprime (r : ℕ) :
    Nat.Coprime (4 * r + 1) 1 := by
  simp

/-- Scalar shadow of the residual `r=1` double-cover obstruction: a fourth
power is already a square. -/
theorem fourth_power_is_square (x : ℂ) :
    x ^ 4 = (x ^ 2) ^ 2 := by
  ring

#print axioms image_class_square_identity
#print axioms genus_gap_identity
#print axioms source_genus_gt_image_genus_of_two_le
#print axioms genus_monotonicity_excludes_two_le
#print axioms genus_monotonicity_forces_parameter_one
#print axioms fiber_image_coordinates_coprime
#print axioms fourth_power_is_square

end Millennium.Hodge.Bidegree24FiberGenusArithmetic
