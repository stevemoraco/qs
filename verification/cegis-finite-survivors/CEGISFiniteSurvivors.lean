import Mathlib

/-! Public hosted replay of three finite/scalar CEGIS survivors. No official Millennium endpoint. -/
namespace Millennium.Crosslane.CEGISFiniteSurvivors

theorem bsd_three_side_square
    (hTop hBot vLeft vRight : ℤ)
    (hSquare : vRight - vLeft = hBot - hTop)
    (hHorizontal : hBot = hTop)
    (hLeft : vLeft = 0) :
    vRight = 0 := by
  omega

theorem ns_absolute_correlation_terminal
    (u v corr theta c R E : ℝ)
    (hu : 0 ≤ u)
    (hv : 0 < v)
    (hTheta : 0 ≤ theta)
    (hCauchy : |corr| ≤ u * v)
    (hCorrelation : theta * v ^ 2 ≤ |corr|)
    (hShell : c * R ≤ v ^ 2)
    (hEnergy : u ^ 2 ≤ E) :
    theta ^ 2 * c * R ≤ E := by
  have hThetaV2 : theta * v ^ 2 ≤ u * v := le_trans hCorrelation hCauchy
  have hThetaV : theta * v ≤ u := by nlinarith
  have hSquare : (theta * v) ^ 2 ≤ u ^ 2 := by
    nlinarith [sq_nonneg (u - theta * v)]
  have hScaledShell : theta ^ 2 * (c * R) ≤ theta ^ 2 * v ^ 2 :=
    mul_le_mul_of_nonneg_left hShell (sq_nonneg theta)
  calc
    theta ^ 2 * c * R = theta ^ 2 * (c * R) := by ring
    _ ≤ theta ^ 2 * v ^ 2 := hScaledShell
    _ = (theta * v) ^ 2 := by ring
    _ ≤ u ^ 2 := hSquare
    _ ≤ E := hEnergy

theorem ym_binary_phase_information_algebra
    (q A B tau delta I : ℝ)
    (hq : 0 ≤ q)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hqA : q ≤ A)
    (hqB : q ≤ B)
    (htau : 0 ≤ tau)
    (hdelta : A * B * tau ≤ delta)
    (hPinA : 2 * delta ^ 2 / A ≤ I)
    (hPinB : 2 * delta ^ 2 / B ≤ I) :
    2 * q ^ 3 * tau ^ 2 ≤ I := by
  have hxnonneg : 0 ≤ A * B * tau :=
    mul_nonneg (mul_nonneg hApos.le hBpos.le) htau
  have hdeltanonneg : 0 ≤ delta := le_trans hxnonneg hdelta
  have hsq : (A * B * tau) ^ 2 ≤ delta ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hdelta)
      (add_nonneg hdeltanonneg hxnonneg)
    nlinarith
  rcases le_total A B with hAB | hBA
  · have hq2B2 : q ^ 2 ≤ B ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hqB)
        (add_nonneg hBpos.le hq)
      nlinarith
    have hq3 : q ^ 3 ≤ A * B ^ 2 := by
      calc
        q ^ 3 = q * q ^ 2 := by ring
        _ ≤ A * B ^ 2 := mul_le_mul hqA hq2B2 (sq_nonneg q) hApos.le
    have hq3A : q ^ 3 * A ≤ A ^ 2 * B ^ 2 := by
      calc
        q ^ 3 * A ≤ (A * B ^ 2) * A :=
          mul_le_mul_of_nonneg_right hq3 hApos.le
        _ = A ^ 2 * B ^ 2 := by ring
    have hcore : q ^ 3 * tau ^ 2 * A ≤ delta ^ 2 := by
      calc
        q ^ 3 * tau ^ 2 * A = (q ^ 3 * A) * tau ^ 2 := by ring
        _ ≤ (A ^ 2 * B ^ 2) * tau ^ 2 :=
          mul_le_mul_of_nonneg_right hq3A (sq_nonneg tau)
        _ = (A * B * tau) ^ 2 := by ring
        _ ≤ delta ^ 2 := hsq
    have htoPin : 2 * q ^ 3 * tau ^ 2 ≤ 2 * delta ^ 2 / A := by
      apply (le_div_iff₀ hApos).2
      nlinarith
    exact le_trans htoPin hPinA
  · have hq2A2 : q ^ 2 ≤ A ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hqA)
        (add_nonneg hApos.le hq)
      nlinarith
    have hq3 : q ^ 3 ≤ A ^ 2 * B := by
      calc
        q ^ 3 = q ^ 2 * q := by ring
        _ ≤ A ^ 2 * B := mul_le_mul hq2A2 hqB hq (sq_nonneg A)
    have hq3B : q ^ 3 * B ≤ A ^ 2 * B ^ 2 := by
      calc
        q ^ 3 * B ≤ (A ^ 2 * B) * B :=
          mul_le_mul_of_nonneg_right hq3 hBpos.le
        _ = A ^ 2 * B ^ 2 := by ring
    have hcore : q ^ 3 * tau ^ 2 * B ≤ delta ^ 2 := by
      calc
        q ^ 3 * tau ^ 2 * B = (q ^ 3 * B) * tau ^ 2 := by ring
        _ ≤ (A ^ 2 * B ^ 2) * tau ^ 2 :=
          mul_le_mul_of_nonneg_right hq3B (sq_nonneg tau)
        _ = (A * B * tau) ^ 2 := by ring
        _ ≤ delta ^ 2 := hsq
    have htoPin : 2 * q ^ 3 * tau ^ 2 ≤ 2 * delta ^ 2 / B := by
      apply (le_div_iff₀ hBpos).2
      nlinarith
    exact le_trans htoPin hPinB

#print axioms bsd_three_side_square
#print axioms ns_absolute_correlation_terminal
#print axioms ym_binary_phase_information_algebra
end Millennium.Crosslane.CEGISFiniteSurvivors
