import Mathlib

namespace Millennium.YangMills

theorem lowWeight_of_positiveTimeCovariance
    {V L C q rho : ℝ}
    (hUpper : C ≤ rho * V + (1 - rho) * L)
    (hLower : q * V ≤ C) :
    (q - rho) * V ≤ (1 - rho) * L := by
  nlinarith

theorem half_lowWeight_of_midpointCovariance
    {V L C rho : ℝ}
    (hV : 0 ≤ V)
    (hrho : rho < 1)
    (hUpper : C ≤ rho * V + (1 - rho) * L)
    (hLower : ((1 + rho) / 2) * V ≤ C) :
    V / 2 ≤ L := by
  have h := lowWeight_of_positiveTimeCovariance
    (V := V) (L := L) (C := C) (q := (1 + rho) / 2) (rho := rho)
    hUpper hLower
  nlinarith

theorem covariance_variance_ratio_invariant_under_rescaling
    (z V C : ℝ) (hz : z ≠ 0) (hV : V ≠ 0) :
    (z^2 * C) / (z^2 * V) = C / V := by
  have hz2 : z^2 ≠ 0 := pow_ne_zero 2 hz
  field_simp [hz2, hV]
  ring

theorem midpoint_covariance_test_iff_under_rescaling
    (z V C rho : ℝ) (hz : z ≠ 0) :
    ((1 + rho) / 2) * (z^2 * V) ≤ z^2 * C ↔
      ((1 + rho) / 2) * V ≤ C := by
  have hz2 : 0 < z^2 := sq_pos_of_ne_zero hz
  have hfactor :
      ((1 + rho) / 2) * (z^2 * V) =
        z^2 * (((1 + rho) / 2) * V) := by ring
  rw [hfactor]
  exact mul_le_mul_iff_of_pos_left hz2

theorem spectral_upper_test_iff_under_rescaling
    (z V L C rho : ℝ) (hz : z ≠ 0) :
    z^2 * C ≤ rho * (z^2 * V) + (1 - rho) * (z^2 * L) ↔
      C ≤ rho * V + (1 - rho) * L := by
  have hz2 : 0 < z^2 := sq_pos_of_ne_zero hz
  have hrhs :
      rho * (z^2 * V) + (1 - rho) * (z^2 * L) =
        z^2 * (rho * V + (1 - rho) * L) := by ring
  rw [hrhs]
  exact mul_le_mul_iff_of_pos_left hz2

theorem renormalized_absolute_lowWeight_of_midpointCovariance
    {z v V L C rho : ℝ}
    (hV : 0 ≤ V)
    (hrho : rho < 1)
    (hUpper : C ≤ rho * V + (1 - rho) * L)
    (hLower : ((1 + rho) / 2) * V ≤ C)
    (hRenormVariance : v ≤ z^2 * V) :
    v / 2 ≤ z^2 * L := by
  have hHalf : V / 2 ≤ L :=
    half_lowWeight_of_midpointCovariance hV hrho hUpper hLower
  have hz2 : 0 ≤ z^2 := sq_nonneg z
  nlinarith

/-- Harmless fresh-replay declaration; not used by substantive theorems. -/
theorem localFieldSpectralRenorm_replay_marker_20260814 : (41 : ℝ) = 41 := rfl

#print axioms covariance_variance_ratio_invariant_under_rescaling
#print axioms midpoint_covariance_test_iff_under_rescaling
#print axioms spectral_upper_test_iff_under_rescaling
#print axioms renormalized_absolute_lowWeight_of_midpointCovariance
#print axioms localFieldSpectralRenorm_replay_marker_20260814

end Millennium.YangMills
