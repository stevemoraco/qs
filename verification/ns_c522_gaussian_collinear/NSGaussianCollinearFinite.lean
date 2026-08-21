import Mathlib

/-!
# Navier–Stokes Gaussian-collinearity finite core

This file formalizes only the positive-semidefinite eigenvalue shadow of the
Gaussian angular-defect identity and the scalar coercivity endpoint. It does
not formalize vorticity, backward-Leray flow, weighted integration by parts,
harmonic distributions, invariant laws, or Navier–Stokes regularity.
-/

namespace NSGaussianCollinearFinite

/-- For nonnegative covariance eigenvalues, zero pairwise-product sum forces
all three pairwise products to vanish. -/
theorem pairwise_products_zero_of_sum_zero
    {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hzero : x * y + x * z + y * z = 0) :
    x * y = 0 ∧ x * z = 0 ∧ y * z = 0 := by
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hxz : 0 ≤ x * z := mul_nonneg hx hz
  have hyz : 0 ≤ y * z := mul_nonneg hy hz
  constructor
  · nlinarith
  · constructor <;> nlinarith

/-- If one covariance eigenvalue is positive and the angular defect vanishes,
the other two eigenvalues vanish. -/
theorem rank_one_shadow_of_first_positive
    {x y z : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hzero : x * y + x * z + y * z = 0) :
    y = 0 ∧ z = 0 := by
  have hpairs := pairwise_products_zero_of_sum_zero (le_of_lt hx) hy hz hzero
  constructor
  · exact (mul_eq_zero.mp hpairs.1).resolve_left (ne_of_gt hx)
  · exact (mul_eq_zero.mp hpairs.2.1).resolve_left (ne_of_gt hx)

/-- Exact scalar form of the covariance angular defect. -/
theorem angular_defect_eigenvalue_identity
    (x y z : ℝ) :
    (x + y + z) ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) =
      2 * (x * y + x * z + y * z) := by
  ring

/-- Zero stretching cannot dominate a strictly positive coercive energy. -/
theorem energy_zero_of_zero_stretching
    {stretch dissipation energy radius coefficient : ℝ}
    (hdiss : 0 ≤ dissipation)
    (henergy : 0 ≤ energy)
    (hradius : 0 ≤ radius)
    (hcoeff : 0 ≤ coefficient)
    (hcoercive : dissipation + energy / 8 + coefficient * radius ≤ stretch)
    (hstretch : stretch = 0) :
    energy = 0 := by
  have hcr : 0 ≤ coefficient * radius := mul_nonneg hcoeff hradius
  nlinarith

/-- The complete finite terminal implication: zero covariance defect gives zero
stretching externally, and coercivity then forces zero energy. -/
theorem collinear_coercive_terminal
    {stretch dissipation energy radius coefficient : ℝ}
    (hdiss : 0 ≤ dissipation)
    (henergy : 0 ≤ energy)
    (hradius : 0 ≤ radius)
    (hcoeff : 0 ≤ coefficient)
    (hcoercive : dissipation + energy / 8 + coefficient * radius ≤ stretch)
    (hcollinearStretch : stretch = 0) :
    energy = 0 := by
  exact energy_zero_of_zero_stretching hdiss henergy hradius hcoeff
    hcoercive hcollinearStretch

#print axioms pairwise_products_zero_of_sum_zero
#print axioms rank_one_shadow_of_first_positive
#print axioms angular_defect_eigenvalue_identity
#print axioms energy_zero_of_zero_stretching
#print axioms collinear_coercive_terminal

end NSGaussianCollinearFinite
