import Mathlib

/-!
Finite arithmetic/polynomial shadow of `stevemoraco/RH` run 18.

Formalized here only:
* the q=1,a=7 bidegree ledger after the human-geometric theorem `alpha | det M`;
* the exact discriminant identity for the G0 cuspidal-plane projection cubic;
* the exact G1 separated plane-projection quadratic discriminant, resultant, and
  full cubic discriminant identities;
* elementary ramification-numerator identities used by the human proofs.

NOT formalized here:
* the K3 source or the Hodge conjecture;
* the F_1 blowdown and identification with plane projection;
* the q=1 Stein-defect argument excluding total alpha ramification;
* G0/G1 resolution graphs, simple-elliptic classification, or finite-flat
  Gorenstein theory;
* the assertion `alpha | det M` itself as a theorem about biform sections;
* the flex interpretation of the G1 collision orbit;
* Miranda/Faenzi--Stipins triple-cover geometry or conductor/index geometry.

No axiom below carries any of those conclusions.
-/

namespace Millennium.Hodge.R3Q1A7AlphaG0G1PlaneFiniteCore

def cubicDisc (a b c d : ℤ) : ℤ :=
  b^2 * c^2 - 4*a*c^3 - 4*b^3*d - 27*a^2*d^2 + 18*a*b*c*d

/-! Degree ledgers after the human geometric alpha-gate theorem. -/

theorem residual_index_parameter_degree :
    (45 : ℤ) - 13 = 32 := by
  norm_num

theorem residual_conductor_bidegree_T :
    2 * (32 : ℤ) + 14 = 78 := by
  norm_num

theorem residual_conductor_bidegree_U :
    2 * (9 : ℤ) + 6 = 24 := by
  norm_num

theorem global_index_parameter_degree :
    3 * (13 : ℤ) + 32 = 71 := by
  norm_num

/-!
G0: after the plane-cubic blowdown the affine projection equation is

  x^3 - u^2 (x-a)^2 = 0.

Its x-coefficients are `1, -u^2, 2*a*u^2, -a^2*u^2`.
-/

theorem g0_plane_projection_discriminant (a u : ℤ) :
    cubicDisc 1 (-u^2) (2*a*u^2) (-a^2*u^2)
      = a^3 * u^4 * (4*u^2 - 27*a) := by
  simp [cubicDisc]
  ring

-- Numerator identity for d/dt [t^3/(t^2-a)].
theorem g0_normalization_derivative_numerator (a t : ℤ) :
    3*t^2*(t^2-a) - 2*t^4 = t^2*(t^2-3*a) := by
  ring

-- The two residual critical points satisfy t^2=3a; their images differ by sign.
theorem g0_residual_branch_value_numerator (a t : ℤ)
    (h : t^2 = 3*a) :
    t^3 = 3*a*t := by
  calc
    t^3 = t * t^2 := by ring
    _ = t * (3*a) := by rw [h]
    _ = 3*a*t := by ring

/-!
G1: for finite smooth projection center P=(p^2,p^3), after removing the fixed
basepoint factor the quadratic factor is

  x^2 + (p^2-u^2)x + p^2(p-u)^2.
-/

theorem g1_quadratic_discriminant (p u : ℤ) :
    (p^2-u^2)^2 - 4*p^2*(p-u)^2
      = -(p-u)^3 * (3*p+u) := by
  ring

-- Evaluation of the quadratic at the removed root x=p^2: the line/quadratic resultant.
theorem g1_resultant_linear_factor (p u : ℤ) :
    p^4 + (p^2-u^2)*p^2 + p^2*(p-u)^2
      = p^3*(3*p-2*u) := by
  ring

/-!
Multiplying the fixed linear factor `(x-p^2)` back into the quadratic gives a
monic cubic with coefficients

  1,
  -u^2,
  2*p^2*u*(u-p),
  -p^4*(p-u)^2.

Its discriminant is the exact separated G1 pattern `3+2+1`.
-/

theorem g1_full_cubic_discriminant (p u : ℤ) :
    cubicDisc 1 (-u^2) (2*p^2*u*(u-p)) (-p^4*(p-u)^2)
      = -p^6 * (p-u)^3 * (3*p-2*u)^2 * (3*p+u) := by
  simp [cubicDisc]
  ring

-- Numerator identity for d/dt [(t^2+p*t+p^2)/(t+p)].
theorem g1_normalization_derivative_numerator (p t : ℤ) :
    (2*t+p)*(t+p) - (t^2+p*t+p^2)
      = t*(t+2*p) := by
  ring

-- Exact distinguished values in denominator-cleared form.
theorem g1_cusp_branch_value (p : ℤ) :
    (0 : ℤ)^2 + p*0 + p^2 = p * (0+p) := by
  ring

theorem g1_residual_branch_value (p : ℤ) :
    (-2*p)^2 + p*(-2*p) + p^2 = (-3*p) * (-2*p+p) := by
  ring

theorem g1_tangent_value (p : ℤ) :
    2 * (p^2 + p*p + p^2) = 3*p * (p+p) := by
  ring

#check residual_index_parameter_degree
#check residual_conductor_bidegree_T
#check residual_conductor_bidegree_U
#check global_index_parameter_degree
#check g0_plane_projection_discriminant
#check g0_normalization_derivative_numerator
#check g0_residual_branch_value_numerator
#check g1_quadratic_discriminant
#check g1_resultant_linear_factor
#check g1_full_cubic_discriminant
#check g1_normalization_derivative_numerator
#check g1_cusp_branch_value
#check g1_residual_branch_value
#check g1_tangent_value

#print axioms residual_index_parameter_degree
#print axioms residual_conductor_bidegree_T
#print axioms residual_conductor_bidegree_U
#print axioms global_index_parameter_degree
#print axioms g0_plane_projection_discriminant
#print axioms g0_normalization_derivative_numerator
#print axioms g0_residual_branch_value_numerator
#print axioms g1_quadratic_discriminant
#print axioms g1_resultant_linear_factor
#print axioms g1_full_cubic_discriminant
#print axioms g1_normalization_derivative_numerator
#print axioms g1_cusp_branch_value
#print axioms g1_residual_branch_value
#print axioms g1_tangent_value

end Millennium.Hodge.R3Q1A7AlphaG0G1PlaneFiniteCore
