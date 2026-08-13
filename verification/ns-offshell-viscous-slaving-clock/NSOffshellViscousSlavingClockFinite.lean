import Mathlib

namespace NSOffshellViscousSlavingClockFinite

/-- Exponent of the dimensionless heat action `Q_N^2 * tau_N` when
`Q_N ~ N^frequencyExponent` and `tau_N ~ N^(-clockExponent)`. -/
def heatActionExponent (frequencyExponent clockExponent : ℝ) : ℝ :=
  2 * frequencyExponent - clockExponent

/-- Heat accumulates a growing action exactly when the clock exponent is below
 twice the frequency exponent. -/
theorem heat_action_positive_iff
    {frequencyExponent clockExponent : ℝ} :
    0 < heatActionExponent frequencyExponent clockExponent ↔
      clockExponent < 2 * frequencyExponent := by
  unfold heatActionExponent
  constructor <;> intro h <;> linarith

/-- The threshold frequency exponent for an `N^alpha` clock is `alpha/2`. -/
theorem critical_frequency_is_neutral
    {alpha : ℝ} :
    heatActionExponent (alpha / 2) alpha = 0 := by
  unfold heatActionExponent
  ring

/-- A fixed-ratio off-shell frequency has exponent one.  On every
superquadratic clock `alpha>2`, its heat action tends in the wrong exponent
direction. -/
theorem fixed_ratio_heat_exponent_negative
    {alpha : ℝ} (halpha : 2 < alpha) :
    heatActionExponent 1 alpha < 0 := by
  unfold heatActionExponent
  norm_num
  linarith

/-- Any frequency exponent capable of producing a growing heat action on a
superquadratic clock must itself be strictly superlinear. -/
theorem genuine_slaving_requires_superlinear_frequency
    {alpha frequencyExponent : ℝ}
    (halpha : 2 < alpha)
    (hslaving : 0 < heatActionExponent frequencyExponent alpha) :
    1 < frequencyExponent := by
  unfold heatActionExponent at hslaving
  linarith

/-- In the strict physical packet window, the critical slaving exponent lies
strictly between one and five quarters. -/
theorem physical_window_slaving_threshold
    {alpha : ℝ}
    (hlower : 2 < alpha)
    (hupper : alpha < 5 / 2) :
    1 < alpha / 2 ∧ alpha / 2 < 5 / 4 := by
  constructor <;> linarith

/-- Abstract retained Duhamel response: `undamped` is the forcing-time product,
and `retention` is the semigroup retention factor. -/
def retainedResponse (undamped retention : ℝ) : ℝ :=
  undamped * retention

/-- If at least half of a nonnegative undamped response survives, the actual
response is at least half of the undamped value. -/
theorem half_retention_floor
    {undamped retention : ℝ}
    (hundamped : 0 ≤ undamped)
    (hretention : 1 / 2 ≤ retention) :
    undamped / 2 ≤ retainedResponse undamped retention := by
  have hnonneg : 0 ≤ undamped * (retention - 1 / 2) :=
    mul_nonneg hundamped (sub_nonneg.mpr hretention)
  unfold retainedResponse
  nlinarith

/-- A scale-independent lower floor in the undamped response survives as a
scale-independent half-floor whenever retention is at least one half. -/
theorem half_retention_preserves_positive_floor
    {floor undamped retention : ℝ}
    (hfloor : 0 ≤ floor)
    (hundamped : floor ≤ undamped)
    (hretention : 1 / 2 ≤ retention) :
    floor / 2 ≤ retainedResponse undamped retention := by
  have hundamped_nonneg : 0 ≤ undamped := le_trans hfloor hundamped
  have hhalf := half_retention_floor hundamped_nonneg hretention
  linarith

/-- Exact coefficient-clock cancellation shell: if forcing times activation
length is `coefficient * duration`, half-retention leaves at least half of that
quantity. -/
theorem coefficient_clock_half_response
    {forcing activation coefficient duration retention : ℝ}
    (hclock : forcing * activation = coefficient * duration)
    (hproduct : 0 ≤ coefficient * duration)
    (hretention : 1 / 2 ≤ retention) :
    coefficient * duration / 2 ≤
      retainedResponse (forcing * activation) retention := by
  rw [hclock]
  exact half_retention_floor hproduct hretention

/-- Include an amplitude exponent `a` when the nonlinear clock is accelerated
by a pump `A_N ~ N^a`. -/
def amplitudeHeatExponent
    (frequencyExponent clockExponent amplitudeExponent : ℝ) : ℝ :=
  2 * frequencyExponent - clockExponent - amplitudeExponent

/-- Positive amplitude growth strictly decreases the heat-action exponent, so
it makes linear viscous slaving harder rather than easier. -/
theorem growing_amplitude_hurts_slaving
    {frequencyExponent clockExponent amplitudeExponent : ℝ}
    (hamplitude : 0 < amplitudeExponent) :
    amplitudeHeatExponent frequencyExponent clockExponent amplitudeExponent <
      heatActionExponent frequencyExponent clockExponent := by
  unfold amplitudeHeatExponent heatActionExponent
  linarith

/-- Fixed-ratio frequencies remain heat-invisible on a superquadratic clock
under every nonnegative pump-amplitude exponent. -/
theorem fixed_ratio_with_nonnegative_amplitude_still_negative
    {alpha amplitudeExponent : ℝ}
    (halpha : 2 < alpha)
    (hamplitude : 0 ≤ amplitudeExponent) :
    amplitudeHeatExponent 1 alpha amplitudeExponent < 0 := by
  unfold amplitudeHeatExponent
  norm_num
  linarith

/-- Representative midpoint `alpha=9/4`: a fixed-ratio leakage mode has exact
heat-action exponent `-1/4`. -/
theorem midpoint_fixed_ratio_exponent :
    heatActionExponent 1 (9 / 4) = -1 / 4 := by
  norm_num [heatActionExponent]

/-- At `alpha=9/4`, a growing heat action requires frequency exponent greater
than `9/8`. -/
theorem midpoint_slaving_threshold
    {frequencyExponent : ℝ}
    (hslaving : 0 < heatActionExponent frequencyExponent (9 / 4)) :
    9 / 8 < frequencyExponent := by
  unfold heatActionExponent at hslaving
  norm_num at hslaving ⊢
  linarith

#print axioms heat_action_positive_iff
#print axioms critical_frequency_is_neutral
#print axioms fixed_ratio_heat_exponent_negative
#print axioms genuine_slaving_requires_superlinear_frequency
#print axioms physical_window_slaving_threshold
#print axioms half_retention_floor
#print axioms half_retention_preserves_positive_floor
#print axioms coefficient_clock_half_response
#print axioms growing_amplitude_hurts_slaving
#print axioms fixed_ratio_with_nonnegative_amplitude_still_negative
#print axioms midpoint_fixed_ratio_exponent
#print axioms midpoint_slaving_threshold

end NSOffshellViscousSlavingClockFinite
