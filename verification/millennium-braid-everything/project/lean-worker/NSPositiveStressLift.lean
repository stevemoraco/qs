import Mathlib

namespace NSPositiveStressLift

/-- For an output wavevector aligned with the first coordinate, this symmetric
matrix lift sends q=(Q,0,0) to the prescribed transverse force f=(0,a,b). -/
theorem aligned_stress_lift_x
    {Q a b : ℝ} (hQ : Q ≠ 0) :
    (0:ℝ) * Q + (a / Q) * 0 + (b / Q) * 0 = 0 := by
  ring

theorem aligned_stress_lift_y
    {Q a b : ℝ} (hQ : Q ≠ 0) :
    (a / Q) * Q + (0:ℝ) * 0 + (0:ℝ) * 0 = a := by
  field_simp

theorem aligned_stress_lift_z
    {Q a b : ℝ} (hQ : Q ≠ 0) :
    (b / Q) * Q + (0:ℝ) * 0 + (0:ℝ) * 0 = b := by
  field_simp

/-- Adding a scalar multiple of the identity changes the product with q only
by a vector parallel to q, hence leaves its transverse y,z components unchanged. -/
theorem isotropic_shift_preserves_y
    {Q a b lambda : ℝ} (hQ : Q ≠ 0) :
    (a / Q) * Q + (lambda:ℝ) * 0 = a := by
  field_simp

theorem isotropic_shift_preserves_z
    {Q a b lambda : ℝ} (hQ : Q ≠ 0) :
    (b / Q) * Q + (lambda:ℝ) * 0 = b := by
  field_simp

#print axioms aligned_stress_lift_x
#print axioms aligned_stress_lift_y
#print axioms aligned_stress_lift_z
#print axioms isotropic_shift_preserves_y
#print axioms isotropic_shift_preserves_z

end NSPositiveStressLift
