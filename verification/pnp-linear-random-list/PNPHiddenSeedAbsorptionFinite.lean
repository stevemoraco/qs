import Mathlib

/-!
# P versus NP hidden-seed absorption arithmetic

Finite scalar bookkeeping for the hidden-seed hard-core transfer.

This file does NOT formalize circuit semantics, the double-counting identity
for finite seed/core incidences, NP uniformity, Chen--Li--Yang, Range Avoidance,
or P versus NP.  The intended finite-set proof supplies the scalar hypotheses
below; these lemmas firewall the exact subtraction/division steps.
-/

namespace MillenniumBraid
namespace PNPHiddenSeedAbsorptionFinite

/-- If local hard-core acceptance contributes at least `rho * W`, at most
`a * W` of those incidences can be absorbed by global positives, and accepted
incidences split into false-positive plus absorbed incidences, then the genuine
false-positive incidence mass is at least `(rho-a) * W`. -/
theorem residualIncidence
    (rho a W acceptedInc absorbedInc falsePosInc : ℚ)
    (hLocal : rho * W ≤ acceptedInc)
    (hSplit : acceptedInc ≤ falsePosInc + absorbedInc)
    (hAbsorb : absorbedInc ≤ a * W) :
    (rho - a) * W ≤ falsePosInc := by
  linarith

/-- Positive gap and positive total incidence make the multiplicity-weight
normalization denominator positive. -/
theorem normalizationPositive
    (rho a W : ℚ)
    (hGap : a < rho)
    (hW : 0 < W) :
    0 < (rho - a) * W := by
  exact mul_pos (sub_pos.mpr hGap) hW

/-- Once a false-positive edge carries at least `(rho-a)W` multiplicity
incidence, normalizing multiplicity by that quantity gives the edge
fractional mass at least one. -/
theorem edgeMassAtLeastOne
    (rho a W falsePosInc : ℚ)
    (hGap : a < rho)
    (hW : 0 < W)
    (hResidual : (rho - a) * W ≤ falsePosInc) :
    1 ≤ falsePosInc / ((rho - a) * W) := by
  have hDen : 0 < (rho - a) * W := normalizationPositive rho a W hGap hW
  exact (le_div_iff₀ hDen).2 (by simpa using hResidual)

/-- If total multiplicity on globally negative points is at most `W`, the
normalized multiplicity weighting has total mass at most `1/(rho-a)`.
This is the scalar fractional-transversal bound. -/
theorem totalMassAtMostInverseGap
    (rho a W residualMultiplicity : ℚ)
    (hGap : a < rho)
    (hW : 0 < W)
    (hMultiplicity : residualMultiplicity ≤ W) :
    residualMultiplicity / ((rho - a) * W) ≤ 1 / (rho - a) := by
  have hGapPos : 0 < rho - a := sub_pos.mpr hGap
  have hDen : 0 < (rho - a) * W := mul_pos hGapPos hW
  apply (div_le_iff₀ hDen).2
  calc
    residualMultiplicity ≤ W := hMultiplicity
    _ = (1 / (rho - a)) * ((rho - a) * W) := by
      field_simp [ne_of_gt hGapPos]

/-- Quarter-density local cores and absorption at most one eighth leave a
residual incidence density of at least one eighth. -/
theorem quarterCoreEighthAbsorption
    (W falsePosInc : ℚ)
    (hW : 0 ≤ W)
    (hResidual : ((1 : ℚ) / 4 - 1 / 8) * W ≤ falsePosInc) :
    W / 8 ≤ falsePosInc := by
  norm_num at hResidual ⊢
  exact hResidual

/-- The corresponding total multiplicity weighting has mass at most eight. -/
theorem quarterCoreEighthTotalMass
    (W residualMultiplicity : ℚ)
    (hW : 0 < W)
    (hMultiplicity : residualMultiplicity ≤ W) :
    residualMultiplicity / ((((1 : ℚ) / 4) - 1 / 8) * W) ≤ 8 := by
  have h := totalMassAtMostInverseGap
      ((1 : ℚ) / 4) (1 / 8) W residualMultiplicity (by norm_num) hW hMultiplicity
  norm_num at h ⊢
  exact h

/-- Congestion is needed only when converting incidence mass into a count of
distinct witnesses.  If each distinct witness can carry at most `d` incidence,
then `gap*W` incidence forces at least `gap*W/d` distinct witnesses. -/
theorem congestionToDistinctWitnesses
    (gap W incidence d distinct : ℚ)
    (hGap : 0 ≤ gap)
    (hW : 0 ≤ W)
    (hD : 0 < d)
    (hResidual : gap * W ≤ incidence)
    (hCongestion : incidence ≤ d * distinct) :
    gap * W / d ≤ distinct := by
  apply (div_le_iff₀ hD).2
  exact hResidual.trans hCongestion

/-- With quarter-density and one-eighth absorption, congestion `d` yields the
unweighted lower bound `W/(8d)` on distinct false-positive witnesses. -/
theorem quarterEighthCongestionDistinct
    (W incidence d distinct : ℚ)
    (hW : 0 ≤ W)
    (hD : 0 < d)
    (hResidual : W / 8 ≤ incidence)
    (hCongestion : incidence ≤ d * distinct) :
    W / (8 * d) ≤ distinct := by
  have h := congestionToDistinctWitnesses
      ((1 : ℚ) / 8) W incidence d distinct (by norm_num) hW hD
      (by simpa using hResidual) hCongestion
  field_simp [ne_of_gt hD] at h ⊢
  nlinarith

#print axioms residualIncidence
#print axioms normalizationPositive
#print axioms edgeMassAtLeastOne
#print axioms totalMassAtMostInverseGap
#print axioms quarterCoreEighthAbsorption
#print axioms quarterCoreEighthTotalMass
#print axioms congestionToDistinctWitnesses
#print axioms quarterEighthCongestionDistinct

end PNPHiddenSeedAbsorptionFinite
end MillenniumBraid
