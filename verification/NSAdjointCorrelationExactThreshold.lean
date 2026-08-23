import Mathlib

namespace Millennium.NavierStokes.AdjointCorrelationExactThreshold

theorem finiteEnergyCorrelationThreshold
    (c R theta vv uv uu E : ℝ)
    (hc : 0 ≤ c)
    (hR : 0 ≤ R)
    (htheta : 0 ≤ theta)
    (hvv0 : 0 ≤ vv)
    (huu0 : 0 ≤ uu)
    (hsize : c * R ≤ vv)
    (henergy : uu ≤ E)
    (hcorr : theta * vv ≤ uv)
    (hcauchy : uv ^ 2 ≤ uu * vv) :
    c * theta ^ 2 * R ≤ E := by
  have htv0 : 0 ≤ theta * vv := mul_nonneg htheta hvv0
  have huv0 : 0 ≤ uv := le_trans htv0 hcorr
  have hprod : 0 ≤ (uv - theta * vv) * (uv + theta * vv) :=
    mul_nonneg (sub_nonneg.mpr hcorr) (add_nonneg huv0 htv0)
  have hsq : (theta * vv) ^ 2 ≤ uv ^ 2 := by
    nlinarith
  by_cases hvv : vv = 0
  · subst vv
    have hcR : c * R = 0 := by
      nlinarith [mul_nonneg hc hR]
    have htarget : c * theta ^ 2 * R = 0 := by
      calc
        c * theta ^ 2 * R = (c * R) * theta ^ 2 := by ring
        _ = 0 := by rw [hcR]; ring
    rw [htarget]
    exact le_trans huu0 henergy
  · have hvvpos : 0 < vv := lt_of_le_of_ne hvv0 (Ne.symm hvv)
    have hsq' : theta ^ 2 * vv * vv ≤ uu * vv := by
      have hchain := le_trans hsq hcauchy
      nlinarith
    have hthetaEnergy : theta ^ 2 * vv ≤ uu := by
      apply (mul_le_mul_right hvvpos).mp
      simpa [mul_assoc] using hsq'
    calc
      c * theta ^ 2 * R = (c * R) * theta ^ 2 := by ring
      _ ≤ vv * theta ^ 2 := mul_le_mul_of_nonneg_right hsize (sq_nonneg theta)
      _ = theta ^ 2 * vv := by ring
      _ ≤ uu := hthetaEnergy
      _ ≤ E := henergy

theorem finiteEnergyCorrelationThreshold_minimalSigns
    (c R theta vv uv uu E : ℝ)
    (hsize : c * R ≤ vv)
    (henergy : uu ≤ E)
    (hcorr : theta * vv ≤ uv)
    (hcauchy : uv ^ 2 ≤ uu * vv)
    (hthetaV0 : 0 ≤ theta * vv)
    (huu0 : 0 ≤ uu) :
    c * theta ^ 2 * R ≤ E := by
  have hsizeTheta : (c * R) * theta ^ 2 ≤ vv * theta ^ 2 :=
    mul_le_mul_of_nonneg_right hsize (sq_nonneg theta)
  by_cases hvv : vv ≤ 0
  · calc
      c * theta ^ 2 * R = (c * R) * theta ^ 2 := by ring
      _ ≤ vv * theta ^ 2 := hsizeTheta
      _ ≤ 0 := mul_nonpos_of_nonpos_left hvv (sq_nonneg theta)
      _ ≤ uu := huu0
      _ ≤ E := henergy
  · have hvvpos : 0 < vv := lt_of_not_ge hvv
    have huv0 : 0 ≤ uv := le_trans hthetaV0 hcorr
    have hprod : 0 ≤ (uv - theta * vv) * (uv + theta * vv) :=
      mul_nonneg (sub_nonneg.mpr hcorr) (add_nonneg huv0 hthetaV0)
    have hsq : (theta * vv) ^ 2 ≤ uv ^ 2 := by
      nlinarith
    have hsq' : theta ^ 2 * vv * vv ≤ uu * vv := by
      have hchain := le_trans hsq hcauchy
      nlinarith
    have hthetaEnergy : theta ^ 2 * vv ≤ uu := by
      apply (mul_le_mul_right hvvpos).mp
      simpa [mul_assoc] using hsq'
    calc
      c * theta ^ 2 * R = (c * R) * theta ^ 2 := by ring
      _ ≤ vv * theta ^ 2 := hsizeTheta
      _ = theta ^ 2 * vv := by ring
      _ ≤ uu := hthetaEnergy
      _ ≤ E := henergy

theorem finiteEnergyCorrelationThreshold_thetaNonnegative
    (c R theta vv uv uu E : ℝ)
    (hsize : c * R ≤ vv)
    (henergy : uu ≤ E)
    (hcorr : theta * vv ≤ uv)
    (hcauchy : uv ^ 2 ≤ uu * vv)
    (huu0 : 0 ≤ uu)
    (htheta : 0 ≤ theta) :
    c * theta ^ 2 * R ≤ E := by
  by_cases hvv : vv ≤ 0
  · have hsizeTheta : (c * R) * theta ^ 2 ≤ vv * theta ^ 2 :=
      mul_le_mul_of_nonneg_right hsize (sq_nonneg theta)
    calc
      c * theta ^ 2 * R = (c * R) * theta ^ 2 := by ring
      _ ≤ vv * theta ^ 2 := hsizeTheta
      _ ≤ 0 := mul_nonpos_of_nonpos_left hvv (sq_nonneg theta)
      _ ≤ uu := huu0
      _ ≤ E := henergy
  · have hvv0 : 0 ≤ vv := le_of_lt (lt_of_not_ge hvv)
    exact finiteEnergyCorrelationThreshold_minimalSigns
      c R theta vv uv uu E hsize henergy hcorr hcauchy
      (mul_nonneg htheta hvv0) huu0

theorem strictThresholdContradiction
    (c R theta vv uv uu E : ℝ)
    (hc : 0 ≤ c)
    (hR : 0 ≤ R)
    (htheta : 0 ≤ theta)
    (hvv0 : 0 ≤ vv)
    (huu0 : 0 ≤ uu)
    (hsize : c * R ≤ vv)
    (henergy : uu ≤ E)
    (hcorr : theta * vv ≤ uv)
    (hcauchy : uv ^ 2 ≤ uu * vv)
    (habove : E < c * theta ^ 2 * R) : False := by
  have hle := finiteEnergyCorrelationThreshold
    c R theta vv uv uu E hc hR htheta hvv0 huu0
    hsize henergy hcorr hcauchy
  linarith

theorem thresholdSharpnessIdentity (c R theta : ℝ) :
    let vv := c * R
    let uu := c * theta ^ 2 * R
    let uv := theta * c * R
    uv ^ 2 = uu * vv := by
  dsimp
  ring

def backwardQuarterTurn (x : ℝ × ℝ) : ℝ × ℝ := (x.2, -x.1)

theorem backwardQuarterTurn_preserves_normSq (x : ℝ × ℝ) :
    (backwardQuarterTurn x).1 ^ 2 + (backwardQuarterTurn x).2 ^ 2 =
      x.1 ^ 2 + x.2 ^ 2 := by
  simp [backwardQuarterTurn]
  ring

theorem backwardQuarterTurn_zero_source_overlap :
    let source : ℝ × ℝ := (1, 0)
    let terminal : ℝ × ℝ := (1, 0)
    let back := backwardQuarterTurn terminal
    back.1 * source.1 + back.2 * source.2 = 0 := by
  norm_num [backwardQuarterTurn]

#print axioms finiteEnergyCorrelationThreshold
#print axioms finiteEnergyCorrelationThreshold_minimalSigns
#print axioms finiteEnergyCorrelationThreshold_thetaNonnegative
#print axioms strictThresholdContradiction
#print axioms thresholdSharpnessIdentity
#print axioms backwardQuarterTurn_preserves_normSq
#print axioms backwardQuarterTurn_zero_source_overlap

end Millennium.NavierStokes.AdjointCorrelationExactThreshold
