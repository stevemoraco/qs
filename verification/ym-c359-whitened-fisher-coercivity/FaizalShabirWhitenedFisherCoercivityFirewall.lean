import Mathlib

namespace Millennium.YangMills.FaizalShabirWhitenedFisherCoercivityFirewall

/-- Scalar shadow of the score/Cramér--Rao argument.
If Cauchy--Schwarz/Stein gives `1 ≤ variance * fisher`, the score second
moment is nonnegative and bounded above by `upper`, then the variance is at
least `1 / upper`. -/
theorem varianceLowerFromScoreUpper
    (variance fisher upper : ℝ)
    (hfisher0 : 0 ≤ fisher)
    (hupper0 : 0 < upper)
    (hfisherUpper : fisher ≤ upper)
    (hcramerRao : 1 ≤ variance * fisher) :
    1 / upper ≤ variance := by
  have hvariance0 : 0 ≤ variance := by
    by_contra h
    have hvarianceNeg : variance < 0 := lt_of_not_ge h
    have hprod : variance * fisher ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hvarianceNeg) hfisher0
    linarith
  have hmul : 1 ≤ variance * upper := by
    have hcomp : variance * fisher ≤ variance * upper :=
      mul_le_mul_of_nonneg_left hfisherUpper hvariance0
    linarith
  exact (div_le_iff₀ hupper0).2 (by simpa [mul_comm] using hmul)

/-- If the score/Fisher second moment is bounded by `1 + delta`, the whitened
source variance has reciprocal coercivity at least `1 / (1 + delta)`. This is
the scalar finite consumer for the matrix statement
`Cov >= (1 + delta)^(-1) I`. -/
theorem varianceLowerFromAveragedCurvature
    (variance fisher delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hfisher0 : 0 ≤ fisher)
    (hfisherUpper : fisher ≤ 1 + delta)
    (hcramerRao : 1 ≤ variance * fisher) :
    1 / (1 + delta) ≤ variance := by
  have hupper0 : 0 < (1 + delta : ℝ) := by linarith
  exact varianceLowerFromScoreUpper
    variance fisher (1 + delta)
    hfisher0 hupper0 hfisherUpper hcramerRao

/-- Reciprocal version used by the implicit-function theorem: if the scalar
source Hessian has lower bound `1 / (1 + delta)`, its inverse is at most
`1 + delta`. -/
theorem inverseBoundFromVarianceLower
    (variance delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hvariance : 1 / (1 + delta) ≤ variance) :
    1 / variance ≤ 1 + delta := by
  have hden : 0 < (1 + delta : ℝ) := by linarith
  have hvarpos : 0 < variance := by
    have hrecippos : 0 < 1 / (1 + delta : ℝ) := one_div_pos.mpr hden
    linarith
  exact (div_le_iff₀ hvarpos).2 (by
    have hmul : 1 ≤ variance * (1 + delta) :=
      (div_le_iff₀ hden).1 hvariance
    simpa [mul_comm] using hmul)

end Millennium.YangMills.FaizalShabirWhitenedFisherCoercivityFirewall
