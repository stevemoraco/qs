import Mathlib

/-!
# Navier--Stokes first-hitting / log-tail finite firewall

Honesty status: this file formalizes only finite scalar ordering and the final
common-scale contradiction used in a conditional Navier--Stokes argument.  It
does not formalize hitting-time existence, Lorentz spaces, BMO commutators,
spatial analyticity, the vorticity equation, a continuation criterion, or any
official Clay theorem.
-/

namespace MillenniumBraid
namespace NSFirstHittingLogTail

/-- A threshold equal to one quarter of a terminal height remains at least one
quarter of every smaller intermediate height. -/
theorem quarterThresholdIsTopFraction
    {height terminal threshold : ℝ}
    (hheight : height ≤ terminal)
    (hthreshold : threshold = terminal / 4) :
    height / 4 ≤ threshold := by
  rw [hthreshold]
  linarith

/-- If a scalar value is at most the truncation level, its positive-part
truncation is exactly zero. -/
theorem zeroTruncationAtThreshold
    {value threshold : ℝ}
    (hvalue : value ≤ threshold) :
    max (value - threshold) 0 = 0 := by
  exact max_eq_right (sub_nonpos.mpr hvalue)

/-- A positive common scale cannot support a lower event bound with a strictly
larger coefficient and an upper event bound with a smaller coefficient. -/
theorem logTailMatchedCoreContradiction
    {coreCoeff tailCoeff scale volume : ℝ}
    (hscale : 0 < scale)
    (hlower : coreCoeff * scale ≤ volume)
    (hupper : volume ≤ tailCoeff * scale)
    (hcoeff : tailCoeff < coreCoeff) :
    False := by
  have hle : coreCoeff * scale ≤ tailCoeff * scale :=
    hlower.trans hupper
  have hlt : tailCoeff * scale < coreCoeff * scale :=
    mul_lt_mul_of_pos_right hcoeff hscale
  exact (not_lt_of_ge hle) hlt

/-- The same firewall with the upper coefficient displayed as a logarithmic
loss.  The analytic proof must separately establish
`upperCoeff / logGain < coreCoeff`. -/
theorem logGainMatchedCoreContradiction
    {coreCoeff upperCoeff logGain scale volume : ℝ}
    (hscale : 0 < scale)
    (hlower : coreCoeff * scale ≤ volume)
    (hupper : volume ≤ (upperCoeff / logGain) * scale)
    (hgain : upperCoeff / logGain < coreCoeff) :
    False := by
  exact logTailMatchedCoreContradiction
    hscale hlower hupper hgain

#print axioms quarterThresholdIsTopFraction
#print axioms zeroTruncationAtThreshold
#print axioms logTailMatchedCoreContradiction
#print axioms logGainMatchedCoreContradiction

end NSFirstHittingLogTail
end MillenniumBraid
