import Mathlib

namespace NSBlobIntermittencyWindow

/-- The nested-localization modulation exponent for `q` localized spatial
directions is `1 - 2(α-1)/q`.  In three dimensions this is positive exactly
below the physical endpoint `α = 5/2`. -/
theorem blob3_window_iff {α : ℝ} :
    0 < 1 - 2 * (α - 1) / 3 ↔ α < 5 / 2 := by
  constructor <;> intro h <;> linarith

/-- Two-dimensional tube localization has positive modulation slack exactly
below `α=2`; hence it cannot cover the viscous Palasek regime `α>2`. -/
theorem tube2_window_iff {α : ℝ} :
    0 < 1 - 2 * (α - 1) / 2 ↔ α < 2 := by
  constructor <;> intro h <;> linarith

/-- Explicit incompatibility of tube localization with viscous intermittency. -/
theorem viscous_tube_no_window {α : ℝ} (hα : 2 < α) :
    1 - 2 * (α - 1) / 2 < 0 := by
  linarith

/-- In the strict physical viscous window, the three-dimensional blob
modulation budget is strictly positive. -/
theorem viscous_blob_has_window {α : ℝ}
    (hlo : 2 < α) (hhi : α < 5 / 2) :
    0 < (5 - 2 * α) / 3 := by
  linarith

/-- The convenient test point α=9/4 leaves exactly 1/6 of exponent slack. -/
theorem alpha_nine_fourths_slack :
    (5 - 2 * (9 / 4 : ℝ)) / 3 = 1 / 6 := by
  norm_num

/-- Any positive modulation exponent below the available 3D slack obeys the
basic carrier/modulation inequality after exponent comparison. -/
theorem modulation_exponent_closes
    {α θ : ℝ}
    (hθ0 : 0 < θ)
    (hθ : θ < (5 - 2 * α) / 3) :
    θ + 2 * (α - 1) / 3 < 1 := by
  linarith

/-- No positive modulation exponent can satisfy the analogous tube inequality
once α is viscous (`α>2`). -/
theorem no_positive_tube_modulation
    {α θ : ℝ}
    (hα : 2 < α)
    (hθ0 : 0 < θ) :
    ¬ (θ + (α - 1) < 1) := by
  intro h
  linarith

#print axioms blob3_window_iff
#print axioms tube2_window_iff
#print axioms viscous_tube_no_window
#print axioms viscous_blob_has_window
#print axioms alpha_nine_fourths_slack
#print axioms modulation_exponent_closes
#print axioms no_positive_tube_modulation

end NSBlobIntermittencyWindow
