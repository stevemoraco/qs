import Mathlib

namespace MillenniumBraid
namespace NSPolarizationRotationFinite

theorem polarizationDenominator_pos (c : ℝ) : 0 < 1 + c ^ 2 := by
  nlinarith [sq_nonneg c]

theorem orthogonalLeakage_nonzero (g c : ℝ) (hg : g ≠ 0) :
    g / (1 + c ^ 2) ≠ 0 := by
  apply div_ne_zero hg
  exact ne_of_gt (polarizationDenominator_pos c)

theorem desired_eq_c_mul_leakage (g c : ℝ) :
    c * (g / (1 + c ^ 2)) = (c * g) / (1 + c ^ 2) := by
  ring

theorem exterior_minus_desired_square_identity (g c : ℝ) :
    (1 + c ^ 2) * g ^ 2 - (c * g) ^ 2 = g ^ 2 := by
  ring

theorem exterior_square_strictly_larger (g c : ℝ) (hg : g ≠ 0) :
    (c * g) ^ 2 < (1 + c ^ 2) * g ^ 2 := by
  have hg2 : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  nlinarith [exterior_minus_desired_square_identity g c]

theorem sum_difference_normal_identity
    (alpha beta gamma delta : ℝ) :
    (alpha * delta - gamma * beta) +
        (alpha * delta + gamma * beta) =
      2 * alpha * delta := by
  ring

theorem pressureKill_nonzeroRelay_forces_nonzero_coefficients
    (alpha beta gamma delta : ℝ)
    (hkill : alpha * delta + gamma * beta = 0)
    (hrelay : alpha * delta - gamma * beta ≠ 0) :
    alpha ≠ 0 ∧ beta ≠ 0 ∧ gamma ≠ 0 ∧ delta ≠ 0 := by
  constructor
  · intro halpha
    subst alpha
    simp at hkill
    apply hrelay
    simp [hkill]
  constructor
  · intro hbeta
    subst beta
    simp at hkill
    apply hrelay
    simp [hkill]
  constructor
  · intro hgamma
    subst gamma
    simp at hkill
    apply hrelay
    simp [hkill]
  · intro hdelta
    subst delta
    simp at hkill
    apply hrelay
    simp [hkill]

theorem normal_not_in_mixed_line
    (planar normal : ℝ)
    (hplanar : planar ≠ 0) :
    ¬ ∃ scale : ℝ, scale * planar = 0 ∧ scale * normal = 1 := by
  rintro ⟨scale, hzero, hone⟩
  have hscale : scale = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hplanar
  subst scale
  norm_num at hone

theorem pressureKill_nonzeroRelay_forces_noninvariance
    (alpha beta gamma delta : ℝ)
    (hkill : alpha * delta + gamma * beta = 0)
    (hrelay : alpha * delta - gamma * beta ≠ 0) :
    (¬ ∃ scale : ℝ, scale * alpha = 0 ∧ scale * beta = 1) ∧
      (¬ ∃ scale : ℝ, scale * gamma = 0 ∧ scale * delta = 1) := by
  rcases pressureKill_nonzeroRelay_forces_nonzero_coefficients
      alpha beta gamma delta hkill hrelay with
    ⟨halpha, _hbeta, hgamma, _hdelta⟩
  exact ⟨normal_not_in_mixed_line alpha beta halpha,
    normal_not_in_mixed_line gamma delta hgamma⟩

theorem skew_normal_energy_cancellation (g A B r s x : ℝ) :
    2 * r * (g * B * x) + 2 * s * (-g * A * x) +
      2 * x * (g * (A * s - B * r)) = 0 := by
  ring

theorem pump_harmonic_acceleration (g A B x : ℝ) :
    g * (A * (-g * A * x) - B * (g * B * x)) =
      -(g ^ 2 * (A ^ 2 + B ^ 2)) * x := by
  ring

theorem skew_characteristic_coefficients (g A B lambda : ℝ) :
    lambda ^ 3 + g ^ 2 * (A ^ 2 + B ^ 2) * lambda =
      lambda * (lambda ^ 2 + g ^ 2 * (A ^ 2 + B ^ 2)) := by
  ring

theorem viscous_normal_energy_identity
    (nu N K g A B r s x : ℝ) :
    2 * r * (-nu * N ^ 2 * r + g * B * x) +
      2 * s * (-nu * N ^ 2 * s - g * A * x) +
      2 * x * (-nu * K ^ 2 * x + g * (A * s - B * r)) =
        -2 * nu * N ^ 2 * (r ^ 2 + s ^ 2) -
          2 * nu * K ^ 2 * x ^ 2 := by
  ring

theorem substantialTransfer_requires_largeRatio
    (transfer ratio energy fraction : ℝ)
    (henergy : 0 < energy)
    (hbound : transfer ≤ ratio * energy)
    (hrequired : fraction * energy ≤ transfer) :
    fraction ≤ ratio := by
  nlinarith

inductive PolarizationSector where
  | chosen
  | orthogonal
  deriving DecidableEq

theorem chosen_ne_orthogonal :
    PolarizationSector.chosen ≠ PolarizationSector.orthogonal := by
  decide

#print axioms polarizationDenominator_pos
#print axioms orthogonalLeakage_nonzero
#print axioms desired_eq_c_mul_leakage
#print axioms exterior_minus_desired_square_identity
#print axioms exterior_square_strictly_larger
#print axioms sum_difference_normal_identity
#print axioms pressureKill_nonzeroRelay_forces_nonzero_coefficients
#print axioms normal_not_in_mixed_line
#print axioms pressureKill_nonzeroRelay_forces_noninvariance
#print axioms skew_normal_energy_cancellation
#print axioms pump_harmonic_acceleration
#print axioms skew_characteristic_coefficients
#print axioms viscous_normal_energy_identity
#print axioms substantialTransfer_requires_largeRatio
#print axioms chosen_ne_orthogonal

end NSPolarizationRotationFinite
end MillenniumBraid
