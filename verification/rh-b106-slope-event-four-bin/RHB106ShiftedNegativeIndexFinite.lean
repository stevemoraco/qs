import Mathlib

/-!
# RH B106B shifted marked-threshold finite core

Finite scalar/order algebra for the rank-one negative-index repackaging of B106.
The analytic prime, matrix-compression, BGST, and RH bridges are intentionally
absent.
-/

namespace RHB106ShiftedNegativeIndexFinite

/-- After shifting by an explicit barrier, nonnegativity is exactly the desired
upper bound on the marked scalar. -/
theorem shifted_nonnegative_iff_upper_bound (barrier value : ℝ) :
    0 ≤ barrier - value ↔ value ≤ barrier := by
  linarith

/-- Strict negativity of the shifted scalar is exactly a barrier violation. -/
theorem shifted_negative_iff_violation (barrier value : ℝ) :
    barrier - value < 0 ↔ barrier < value := by
  linarith

/-- A bounded additive matrix/archimedean correction is safely absorbed into
an enlarged scalar barrier. -/
theorem bounded_correction_shift
    {raw marked barrier M : ℝ}
    (herr : |raw - marked| ≤ M)
    (hmarked : marked ≤ barrier) :
    raw ≤ barrier + M := by
  have hup : raw - marked ≤ M := (abs_le.mp herr).2
  linarith

/-- Conversely, a barrier violation deeper than the full bounded correction
survives transfer to the raw marked scalar. -/
theorem deep_violation_survives_bounded_correction
    {raw marked barrier M : ℝ}
    (herr : |raw - marked| ≤ M)
    (hdeep : barrier + M < marked) :
    barrier < raw := by
  have hlo : -M ≤ raw - marked := (abs_le.mp herr).1
  linarith

/-- Two event orbits need no matrix assembly: checking the two shifted scalars is
exactly checking their conjunction. -/
theorem two_event_shifted_threshold
    (bMinus vMinus bPlus vPlus : ℝ) :
    (0 ≤ bMinus - vMinus ∧ 0 ≤ bPlus - vPlus) ↔
      (vMinus ≤ bMinus ∧ vPlus ≤ bPlus) := by
  constructor
  · rintro ⟨hm, hp⟩
    exact ⟨(shifted_nonnegative_iff_upper_bound bMinus vMinus).mp hm,
      (shifted_nonnegative_iff_upper_bound bPlus vPlus).mp hp⟩
  · rintro ⟨hm, hp⟩
    exact ⟨(shifted_nonnegative_iff_upper_bound bMinus vMinus).mpr hm,
      (shifted_nonnegative_iff_upper_bound bPlus vPlus).mpr hp⟩

#print axioms shifted_nonnegative_iff_upper_bound
#print axioms shifted_negative_iff_violation
#print axioms bounded_correction_shift
#print axioms deep_violation_survives_bounded_correction
#print axioms two_event_shifted_threshold

end RHB106ShiftedNegativeIndexFinite
