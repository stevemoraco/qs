import Mathlib
namespace NSAOCriticalPitchRatio

theorem critical_pitch_identity
    {beta r Omega Wp OmegaP q : ℝ}
    (hWp : Wp ≠ 0)
    (hcrit : beta * Wp - OmegaP = 0)
    (hpitch : q = -(2 * r * Omega + r ^ 2 * OmegaP) / Wp) :
    q = -beta * r ^ 2 - 2 * r * (Omega / Wp) := by
  have hOmegaP : OmegaP = beta * Wp := by linarith
  rw [hpitch, hOmegaP]
  field_simp [hWp]
  ring

theorem positive_pitch_forces_ratio_floor
    {beta r Omega Wp q : ℝ}
    (hbeta : 0 < beta) (hr : 0 < r) (hq : 0 < q)
    (hidentity : q = -beta * r ^ 2 - 2 * r * (Omega / Wp)) :
    beta * r / 2 < |Omega / Wp| := by
  let x : ℝ := Omega / Wp
  have hidentity' : q = -beta * r ^ 2 - 2 * r * x := by simpa [x] using hidentity
  have hbase : beta * r ^ 2 < -2 * r * x := by
    rw [hidentity'] at hq
    nlinarith
  have hfact : r * (beta * r) < r * (-2 * x) := by nlinarith
  have hsmall : beta * r < -2 * x := (mul_lt_mul_left hr).mp hfact
  have hxneg : x < 0 := by nlinarith [hbeta, hr, hsmall]
  change beta * r / 2 < |x|
  rw [abs_of_neg hxneg]
  nlinarith

theorem no_positive_pitch_with_small_ratio
    {beta r Omega Wp q : ℝ}
    (hbeta : 0 < beta) (hr : 0 < r) (hq : 0 < q)
    (hidentity : q = -beta * r ^ 2 - 2 * r * (Omega / Wp))
    (hsmall : |Omega / Wp| ≤ beta * r / 2) : False := by
  exact (not_lt_of_ge hsmall)
    (positive_pitch_forces_ratio_floor hbeta hr hq hidentity)

#print axioms critical_pitch_identity
#print axioms positive_pitch_forces_ratio_floor
#print axioms no_positive_pitch_with_small_ratio
end NSAOCriticalPitchRatio
