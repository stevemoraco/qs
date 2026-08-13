import Mathlib

namespace NSBandlimitedStressWindow

/-- Required physical-localization bandwidth exponent is below the parent carrier exponent exactly below alpha=5/2. -/
theorem localization_bandwidth_iff {alpha : ℝ} :
    2*(alpha-1)/3 < 1 ↔ alpha < (5:ℝ)/2 := by
  constructor <;> intro h <;> linarith

/-- Child-carrier separation has positive exponent whenever b>1. -/
theorem carrier_separation_pos {b : ℝ} (hb : 1 < b) :
    0 < b-1 := sub_pos.mpr hb

/-- Parent-band / child-carrier ratio has exponent 1-b, which is strictly negative for b>1. -/
theorem divergence_corrector_exponent_neg {b : ℝ} (hb : 1 < b) :
    1-b < 0 := sub_neg.mpr hb

/-- The child carrier exponent exceeds the physical-localization bandwidth exponent throughout the strict physical window. -/
theorem child_beats_localization
    {alpha b : ℝ} (ha : alpha < (5:ℝ)/2) (hb : 1 < b) :
    2*(alpha-1)/3 < b := by
  have hloc : 2*(alpha-1)/3 < 1 := (localization_bandwidth_iff).2 ha
  linarith

#print axioms localization_bandwidth_iff
#print axioms carrier_separation_pos
#print axioms divergence_corrector_exponent_neg
#print axioms child_beats_localization

end NSBandlimitedStressWindow
