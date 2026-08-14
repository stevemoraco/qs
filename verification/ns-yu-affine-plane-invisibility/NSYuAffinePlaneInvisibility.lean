import Mathlib

/-!
# Yu affine-plane invisibility finite core

Finite real algebra only.  These statements isolate a hostile model for the
Runlong Yu filtered-vorticity route: an affine incompressible Navier--Stokes
profile can have a repeated positive strain plane, spatially constant vorticity
direction, positive strain work, and a centered affine covariance that is
spatially constant (hence invisible to a differentiated-commutator test).

The file does **not** formalize derivatives, filters, Yu's PDE theorem, an
energy-class solution, a singular profile, or Navier--Stokes regularity/blow-up.
The corresponding human note records the exact affine solution and the
infinite-energy boundary.
-/

namespace NSYuAffinePlaneInvisibility

/-- Divergence arithmetic for the affine velocity gradient
`diag(1,1,-2)` plus a skew `y-z` rotation block. -/
theorem affine_plane_divergence :
    (1 : ℝ) + 1 - 2 = 0 := by
  norm_num

/-- The `x`-component of curl for the skew block is `2*b`. -/
theorem affine_plane_vorticity_x (b : ℝ) :
    b - (-b) = 2 * b := by
  ring

/-- Componentwise algebra for the exact affine Navier--Stokes ansatz

`u = (x, y - b z, b y - 2 z)`

when the scalar time derivative satisfies `b_t=b`.  The three groups are
`partial_t u + (u dot grad)u + grad p`; the affine Laplacian is zero.
The pressure gradient used here is
`(-x, (b^2-1)y, (b^2-4)z)`.
-/
theorem affine_plane_ns_residual
    (b bt x y z : ℝ) (hbt : bt = b) :
    (0 + x + (-x) = 0) ∧
    ((-bt * z) + ((1 - b ^ 2) * y + b * z) + ((b ^ 2 - 1) * y) = 0) ∧
    ((bt * y) + ((-b * y) + (4 - b ^ 2) * z) + ((b ^ 2 - 4) * z) = 0) := by
  subst bt
  constructor
  · ring
  constructor <;> ring

/-- The symmetric strain has a repeated top eigenvalue in the affine model. -/
theorem affine_plane_repeated_top_eigenvalue :
    ((1 : ℝ) = 1) ∧ ((-2 : ℝ) < 1) := by
  norm_num

/-- For the actual vorticity `(2*b,0,0)`, the biaxial strain
`diag(1,1,-2)` produces the full positive quadratic work `(2*b)^2`. -/
theorem affine_plane_stretching_identity (b : ℝ) :
    (1 : ℝ) * (2 * b) ^ 2 + 1 * 0 ^ 2 + (-2) * 0 ^ 2 = (2 * b) ^ 2 := by
  ring

/-- Nonzero affine vorticity gives strictly positive strain work. -/
theorem affine_plane_stretching_positive
    (b : ℝ) (hb : b ≠ 0) :
    0 < (2 * b) ^ 2 := by
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hb)

/-- Smallest firewall against the shortcut
`vanishing pairwise direction defect -> vanishing total stretching`.
The direction can be spatially identical while the external affine strain does
strictly positive work. -/
theorem zero_direction_defect_with_positive_affine_work
    (b : ℝ) (hb : b ≠ 0) :
    (((1 : ℝ) - 1) ^ 2 = 0) ∧ 0 < (2 * b) ^ 2 := by
  constructor
  · norm_num
  · exact affine_plane_stretching_positive b hb

/-- A centered two-point filter applied to a scalar affine field has a covariance
that is independent of the base point.  This is the finite algebraic core of
why an affine subgrid stress can be nonzero while its spatial derivative is
zero. -/
theorem centered_affine_covariance_constant
    (a x h : ℝ) :
    ((a * (x + h)) ^ 2 + (a * (x - h)) ^ 2) / 2 - (a * x) ^ 2 = (a * h) ^ 2 := by
  ring

/-- The centered affine covariance takes the same value at every two base
points. -/
theorem centered_affine_covariance_position_independent
    (a x y h : ℝ) :
    (((a * (x + h)) ^ 2 + (a * (x - h)) ^ 2) / 2 - (a * x) ^ 2) =
      (((a * (y + h)) ^ 2 + (a * (y - h)) ^ 2) / 2 - (a * y) ^ 2) := by
  rw [centered_affine_covariance_constant a x h,
    centered_affine_covariance_constant a y h]

/-- A nontrivial affine centered covariance may be strictly positive and still
be spatially constant.  This is the finite no-free-lunch model for trying to
charge an asymptotically affine obstruction solely to a differentiated
commutator. -/
theorem nonzero_affine_covariance_can_be_derivative_invisible
    (a h : ℝ) (ha : a ≠ 0) (hh : h ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ,
        ((a * (x + h)) ^ 2 + (a * (x - h)) ^ 2) / 2 - (a * x) ^ 2 = c := by
  refine ⟨(a * h) ^ 2, sq_pos_of_ne_zero (mul_ne_zero ha hh), ?_⟩
  intro x
  exact centered_affine_covariance_constant a x h

#print axioms affine_plane_divergence
#print axioms affine_plane_vorticity_x
#print axioms affine_plane_ns_residual
#print axioms affine_plane_repeated_top_eigenvalue
#print axioms affine_plane_stretching_identity
#print axioms affine_plane_stretching_positive
#print axioms zero_direction_defect_with_positive_affine_work
#print axioms centered_affine_covariance_constant
#print axioms centered_affine_covariance_position_independent
#print axioms nonzero_affine_covariance_can_be_derivative_invisible

end NSYuAffinePlaneInvisibility
