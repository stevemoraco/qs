import Mathlib

/-!
# P versus NP sharp absorbed-core arithmetic

Finite scalar bookkeeping for the sharp hidden-core transfer and the
conditional-expectation buried-slice selection.

This file does NOT formalize circuit semantics, finite-list double counting,
probability spaces, the random circuit-counting theorem, NP uniformity,
Chen--Li--Yang, or P versus NP. Those interfaces must supply the hypotheses
below. The lemmas firewall the exact rational subtraction and division.
-/

namespace MillenniumBraid
namespace PNPSharpBuriedSliceFinite

/-- If residual multiplicity on global negatives is at most `(1-a)W`, then
normalization by the surviving local demand `(rho-a)W` has total mass at most
the sharp ratio `(1-a)/(rho-a)`. -/
theorem totalMassAtMostSharp
    (rho a W residualMultiplicity : ℚ)
    (hGap : a < rho)
    (hW : 0 < W)
    (hResidual : residualMultiplicity ≤ (1 - a) * W) :
    residualMultiplicity / ((rho - a) * W) ≤ (1 - a) / (rho - a) := by
  have hGapPos : 0 < rho - a := sub_pos.mpr hGap
  have hDen : 0 < (rho - a) * W := mul_pos hGapPos hW
  apply (div_le_iff₀ hDen).2
  calc
    residualMultiplicity ≤ (1 - a) * W := hResidual
    _ = ((1 - a) / (rho - a)) * ((rho - a) * W) := by
      field_simp [ne_of_gt hGapPos]

/-- If the residual multiplicity is exactly `(1-a)W`, the normalized mass is
exactly the sharp ratio. -/
theorem totalMassExactlySharp
    (rho a W residualMultiplicity : ℚ)
    (hGap : a < rho)
    (hW : 0 < W)
    (hResidual : residualMultiplicity = (1 - a) * W) :
    residualMultiplicity / ((rho - a) * W) = (1 - a) / (rho - a) := by
  subst residualMultiplicity
  have hGapPos : 0 < rho - a := sub_pos.mpr hGap
  have hWNe : W ≠ 0 := ne_of_gt hW
  field_simp [ne_of_gt hGapPos, hWNe]

/-- Quarter-density and one-eighth absorption give total mass at most seven,
not merely eight. -/
theorem quarterCoreEighthSharpMass
    (W residualMultiplicity : ℚ)
    (hW : 0 < W)
    (hResidual : residualMultiplicity ≤ ((1 : ℚ) - 1 / 8) * W) :
    residualMultiplicity /
        ((((1 : ℚ) / 4) - 1 / 8) * W) ≤ 7 := by
  have h := totalMassAtMostSharp
      ((1 : ℚ) / 4) (1 / 8) W residualMultiplicity
      (by norm_num) hW hResidual
  norm_num at h ⊢
  exact h

/-- The sharp ratio is monotone increasing in absorption on `a < rho ≤ 1`. -/
theorem sharpRatioMonotone
    (rho a b : ℚ)
    (ha : a < rho)
    (hb : b < rho)
    (hab : a ≤ b)
    (hRho : rho ≤ 1) :
    (1 - a) / (rho - a) ≤ (1 - b) / (rho - b) := by
  have hda : 0 < rho - a := sub_pos.mpr ha
  have hdb : 0 < rho - b := sub_pos.mpr hb
  apply (div_le_div_iff₀ hda hdb).2
  have hprod : 0 ≤ (b - a) * (1 - rho) :=
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hRho)
  nlinarith

/-- At quarter density, the sharp ratio is `4` plus the exact absorption
penalty `12a/(1-4a)`. -/
theorem quarterSharpRatioIdentity
    (a : ℚ)
    (ha : a < (1 : ℚ) / 4) :
    (1 - a) / (((1 : ℚ) / 4) - a) =
      4 + (12 * a) / (1 - 4 * a) := by
  have hDen₁ : ((1 : ℚ) / 4) - a ≠ 0 :=
    ne_of_gt (sub_pos.mpr ha)
  have hDen₂ : 1 - 4 * a ≠ 0 := by
    nlinarith
  field_simp [hDen₁, hDen₂]
  <;> ring

/-- Elementary conditional-average step: if a good event has probability `p`
and contributes `p * goodMean` to at most the total mean, then its conditional
mean is at most `totalMean/p`. -/
theorem conditionalMeanAtMost
    (p goodMean totalMean : ℚ)
    (hp : 0 < p)
    (hContribution : p * goodMean ≤ totalMean) :
    goodMean ≤ totalMean / p := by
  apply (le_div_iff₀ hp).2
  simpa [mul_comm] using hContribution

/-- A finite good event of positive probability contains an outcome no larger
than its conditional mean. The finite-set averaging step supplies `selected`
and the first inequality below. -/
theorem selectedOutcomeAtMostUnconditionalOverGoodMass
    (p selected conditionalMean totalMean : ℚ)
    (hp : 0 < p)
    (hSelected : selected ≤ conditionalMean)
    (hContribution : p * conditionalMean ≤ totalMean) :
    selected ≤ totalMean / p := by
  exact hSelected.trans
    (conditionalMeanAtMost p conditionalMean totalMean hp hContribution)

#print axioms totalMassAtMostSharp
#print axioms totalMassExactlySharp
#print axioms quarterCoreEighthSharpMass
#print axioms sharpRatioMonotone
#print axioms quarterSharpRatioIdentity
#print axioms conditionalMeanAtMost
#print axioms selectedOutcomeAtMostUnconditionalOverGoodMass

end PNPSharpBuriedSliceFinite
end MillenniumBraid
