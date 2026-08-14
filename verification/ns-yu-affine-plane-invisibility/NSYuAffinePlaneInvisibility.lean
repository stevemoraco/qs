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

theorem affine_plane_divergence :
    (1 : ℝ) + 1 - 2 = 0 := by
  norm_num

theorem affine_plane_vorticity_x (b : ℝ) :
    b - (-b) = 2 * b := by
  ring

theorem affine_plane_ns_residual
    (b bt x y z : ℝ) (hbt : bt = b) :
    (0 + x + (-x) = 0) ∧
    ((-bt * z) + ((1 - b ^ 2) * y + b * z) + ((b ^ 2 - 1) * y) = 0) ∧
    ((bt * y) + ((-b * y) + (4 - b ^ 2) * z) + ((b ^ 2 - 4) * z) = 0) := by
  subst bt
  constructor
  · ring
  constructor <;> ring

theorem affine_plane_repeated_top_eigenvalue :
    ((1 : ℝ) = 1) ∧ ((-2 : ℝ) < 1) := by
  norm_num

theorem affine_plane_stretching_identity (b : ℝ) :
    (1 : ℝ) * (2 * b) ^ 2 + 1 * 0 ^ 2 + (-2) * 0 ^ 2 = (2 * b) ^ 2 := by
  ring

theorem affine_plane_stretching_positive
    (b : ℝ) (hb : b ≠ 0) :
    0 < (2 * b) ^ 2 := by
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hb)

theorem zero_direction_defect_with_positive_affine_work
    (b : ℝ) (hb : b ≠ 0) :
    (((1 : ℝ) - 1) ^ 2 = 0) ∧ 0 < (2 * b) ^ 2 := by
  constructor
  · norm_num
  · exact affine_plane_stretching_positive b hb

theorem centered_affine_covariance_constant
    (a x h : ℝ) :
    ((a * (x + h)) ^ 2 + (a * (x - h)) ^ 2) / 2 - (a * x) ^ 2 = (a * h) ^ 2 := by
  ring

theorem centered_affine_covariance_position_independent
    (a x y h : ℝ) :
    (((a * (x + h)) ^ 2 + (a * (x - h)) ^ 2) / 2 - (a * x) ^ 2) =
      (((a * (y + h)) ^ 2 + (a * (y - h)) ^ 2) / 2 - (a * y) ^ 2) := by
  rw [centered_affine_covariance_constant a x h,
    centered_affine_covariance_constant a y h]

theorem nonzero_affine_covariance_can_be_derivative_invisible
    (a h : ℝ) (ha : a ≠ 0) (hh : h ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : ℝ,
        ((a * (x + h)) ^ 2 + (a * (x - h)) ^ 2) / 2 - (a * x) ^ 2 = c := by
  refine ⟨(a * h) ^ 2, sq_pos_of_ne_zero (mul_ne_zero ha hh), ?_⟩
  intro x
  exact centered_affine_covariance_constant a x h

/-- Finite expanding-ball growth gate.  If an affine scalar component has
visible slope `|a| >= gamma` and is bounded by `M` at both endpoints `0` and
`R`, then `gamma * R <= 2 M`. -/
theorem bounded_affine_endpoints_control_visible_slope
    (a c R M gamma : ℝ)
    (hR : 0 ≤ R)
    (hslope : gamma ≤ |a|)
    (h0 : |c| ≤ M)
    (hRbound : |a * R + c| ≤ M) :
    gamma * R ≤ 2 * M := by
  have htri : |a * R| ≤ |a * R + c| + |c| := by
    calc
      |a * R| = |(a * R + c) + (-c)| := by
        rw [show (a * R + c) + (-c) = a * R by ring]
      _ ≤ |a * R + c| + |-c| := abs_add_le _ _
      _ = |a * R + c| + |c| := by rw [abs_neg]
  have hAR : |a| * R ≤ 2 * M := by
    calc
      |a| * R = |a| * |R| := by rw [abs_of_nonneg hR]
      _ = |a * R| := (abs_mul a R).symm
      _ ≤ |a * R + c| + |c| := htri
      _ ≤ M + M := add_le_add hRbound h0
      _ = 2 * M := by ring
  exact le_trans (mul_le_mul_of_nonneg_right hslope hR) hAR

theorem visible_affine_slope_breaks_uniform_ball_bound
    (a c R M gamma : ℝ)
    (hR : 0 ≤ R)
    (hslope : gamma ≤ |a|)
    (hlarge : 2 * M < gamma * R) :
    ¬ (|c| ≤ M ∧ |a * R + c| ≤ M) := by
  rintro ⟨h0, hRbound⟩
  have hsmall := bounded_affine_endpoints_control_visible_slope
    a c R M gamma hR hslope h0 hRbound
  linarith

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
#print axioms bounded_affine_endpoints_control_visible_slope
#print axioms visible_affine_slope_breaks_uniform_ball_bound

end NSYuAffinePlaneInvisibility
