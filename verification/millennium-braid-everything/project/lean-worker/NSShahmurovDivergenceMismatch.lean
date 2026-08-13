import Mathlib

namespace NSShahmurovDivergenceMismatch

/-- If the same physical radial/axial velocity satisfies both true 3D
axisymmetric incompressibility and the claimed 5D radial divergence law,
then the radial component must vanish away from the axis. -/
theorem radial_component_zero
    {r ur dur dzuz : ℝ}
    (hr : r ≠ 0)
    (h3d : dur + ur / r + dzuz = 0)
    (h5d : dur + 3 * ur / r + dzuz = 0) :
    ur = 0 := by
  have h : 2 * ur / r = 0 := by linarith
  have hr2 : (2 : ℝ) / r ≠ 0 := by
    field_simp [hr]
  exact (mul_eq_zero.mp (by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h)).resolve_left (by norm_num)

/-- More directly, true 3D incompressibility determines the auxiliary 5D
weighted divergence as `2 ur/r`, not zero. -/
theorem true3d_implies_weighted5d_divergence
    {r ur dur dzuz : ℝ}
    (h3d : dur + ur / r + dzuz = 0) :
    dur + 3 * ur / r + dzuz = 2 * ur / r := by
  linarith

/-- Conversely, a field made divergence-free for the `r^3` measure has true
3D divergence `-2 ur/r`. -/
theorem weighted5d_implies_true3d_defect
    {r ur dur dzuz : ℝ}
    (h5d : dur + 3 * ur / r + dzuz = 0) :
    dur + ur / r + dzuz = -2 * ur / r := by
  linarith

/-- If both divergence laws hold, the axial derivative also vanishes once the
radial derivative is known to vanish. This small theorem keeps that extra
hypothesis explicit rather than smuggling in decay or localization. -/
theorem axial_derivative_zero_if_radial_derivative_zero
    {r ur dur dzuz : ℝ}
    (h3d : dur + ur / r + dzuz = 0)
    (hur : ur = 0)
    (hdur : dur = 0) :
    dzuz = 0 := by
  subst hur
  subst hdur
  norm_num at h3d ⊢
  exact h3d

#print axioms radial_component_zero
#print axioms true3d_implies_weighted5d_divergence
#print axioms weighted5d_implies_true3d_defect
#print axioms axial_derivative_zero_if_radial_derivative_zero

end NSShahmurovDivergenceMismatch
