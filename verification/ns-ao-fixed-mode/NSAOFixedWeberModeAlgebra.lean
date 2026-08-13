import Mathlib

namespace Millennium.NavierStokes

theorem ao_weber_current_coefficient (ell kappa xi : ℝ) :
    -ell * kappa + 2 * kappa ^ 2 * xi ^ 2 =
      kappa * (2 * kappa * xi ^ 2 - ell) := by
  ring

theorem ao_odd_mode_current_center_identity (ell kappa rho : ℝ) :
    4 * kappa ^ 2 * rho
        + (-ell * kappa) * (-2 * ell * kappa * rho) =
      2 * (ell ^ 2 + 2) * kappa ^ 2 * rho := by
  ring

theorem ao_even_mode_current_center_identity (ell kappa slopeSq : ℝ) :
    (-ell * kappa) * (2 * slopeSq) =
      -2 * ell * kappa * slopeSq := by
  ring

theorem ao_odd_mode_b_response_negative
    (ell kappa rho : ℝ)
    (hell : 0 < ell) (hkappa : 0 < kappa) (hrho : 0 < rho) :
    -2 * ell * kappa * rho < 0 := by
  have hpos : 0 < 2 * ell * kappa * rho := by positivity
  linarith

theorem ao_odd_mode_curvature_response_positive
    (ell kappa rho : ℝ)
    (hkappa : 0 < kappa) (hrho : 0 < rho) :
    0 < 2 * (ell ^ 2 + 2) * kappa ^ 2 * rho := by
  have hsum : 0 < ell ^ 2 + 2 := by nlinarith [sq_nonneg ell]
  have hkappaSq : 0 < kappa ^ 2 := sq_pos_of_pos hkappa
  exact mul_pos (mul_pos (mul_pos (by norm_num) hsum) hkappaSq) hrho

theorem ao_even_mode_b_response_positive
    (slopeSq : ℝ) (hslope : 0 < slopeSq) :
    0 < 2 * slopeSq := by
  positivity

theorem ao_even_mode_curvature_response_negative
    (ell kappa slopeSq : ℝ)
    (hell : 0 < ell) (hkappa : 0 < kappa)
    (hslope : 0 < slopeSq) :
    -2 * ell * kappa * slopeSq < 0 := by
  have hpos : 0 < 2 * ell * kappa * slopeSq := by positivity
  linarith

theorem ao_odd_mode_center_anti_alignment
    (ell kappa rho : ℝ)
    (hell : 0 < ell) (hkappa : 0 < kappa) (hrho : 0 < rho) :
    (2 * (ell ^ 2 + 2) * kappa ^ 2 * rho) *
        (-2 * ell * kappa * rho) < 0 := by
  have hcurv := ao_odd_mode_curvature_response_positive ell kappa rho hkappa hrho
  have hb := ao_odd_mode_b_response_negative ell kappa rho hell hkappa hrho
  exact mul_neg_of_pos_of_neg hcurv hb

theorem ao_even_mode_center_anti_alignment
    (ell kappa slopeSq : ℝ)
    (hell : 0 < ell) (hkappa : 0 < kappa)
    (hslope : 0 < slopeSq) :
    (-2 * ell * kappa * slopeSq) * (2 * slopeSq) < 0 := by
  have hcurv :=
    ao_even_mode_curvature_response_negative ell kappa slopeSq hell hkappa hslope
  have hb := ao_even_mode_b_response_positive slopeSq hslope
  exact mul_neg_of_neg_of_pos hcurv hb

theorem ao_center_anti_alignment_excludes_joint_increase
    (bDot cDot : ℝ) (hanti : cDot * bDot < 0) :
    ¬ (0 < bDot ∧ 0 < cDot) := by
  intro h
  have hpos : 0 < cDot * bDot := mul_pos h.2 h.1
  linarith

theorem ao_odd_mode_fuel_derivative_zero
    (ell a y z xDot qDot : ℝ)
    (hx : xDot = (ell ^ 2 + 2) * a * y * z)
    (hq : qDot = -(ell / 2) * z) :
    ell * xDot + 2 * a * y * (ell ^ 2 + 2) * qDot = 0 := by
  rw [hx, hq]
  ring

theorem ao_even_mode_fuel_derivative_zero
    (ell a y z xDot qDot : ℝ)
    (hx : xDot = -ell * a * y * z)
    (hq : qDot = z / 2) :
    xDot + 2 * ell * a * y * qDot = 0 := by
  rw [hx, hq]
  ring

theorem ao_affine_rate_integrates_to_fuel_invariant
    (x0 x1 q0 q1 weight : ℝ)
    (h : x1 - x0 = -weight * (q1 - q0)) :
    x1 + weight * q1 = x0 + weight * q0 := by
  linarith

theorem ao_ground_mode_chi : (1 : ℝ) + 2 / 1 = 3 := by
  norm_num

theorem ao_ground_mode_invariant_factor (a sqrtN : ℝ) :
    2 * a * sqrtN * ((1 : ℝ) + 2 / 1) = 6 * a * sqrtN := by
  ring

end Millennium.NavierStokes
