import Mathlib

/-!
# Navier–Stokes Yu active-endpoint finite stability core

Finite real-algebra only.

These lemmas support the human Type-I research reduction that, after extracting a
smooth ancient profile and restricting to a compact set on which the true
vorticity magnitude is bounded below, sufficiently small mollifier error cannot
erase a genuine direction gap or its magnitude-weighted pair contribution.

This file does **not** formalize convolution, vorticity, direction normalization,
Runlong Yu's pairwise defect, dominated convergence, analyticity, Giga–Miura,
Navier–Stokes, or any Clay theorem.
-/

namespace NSYuActiveEndpointStability

/-- A lower magnitude bound survives an additive error of at most half the
reference lower bound.  No sign assumption on `kappa` is needed for this affine
inequality. -/
theorem magnitude_floor_after_half_error
    {kappa raw filtered : ℝ}
    (hraw : kappa ≤ raw)
    (herr : |filtered - raw| ≤ kappa / 2) :
    kappa / 2 ≤ filtered := by
  have hlow : -(kappa / 2) ≤ filtered - raw := (abs_le.mp herr).1
  linarith

/-- Two direction perturbations, each at most one quarter of the original gap,
preserve at least half of that gap.  Nonnegativity of the error variables is
unnecessary: only their upper error budgets enter the conclusion. -/
theorem direction_gap_survives_two_quarter_errors
    {delta rawGap filteredGap err₁ err₂ : ℝ}
    (hraw : delta ≤ rawGap)
    (hbudget₁ : err₁ ≤ delta / 4)
    (hbudget₂ : err₂ ≤ delta / 4)
    (htransfer : rawGap - err₁ - err₂ ≤ filteredGap) :
    delta / 2 ≤ filteredGap := by
  linarith

/-- Once both filtered magnitudes retain half of `kappa` and the filtered
angular gap retains half of `delta`, the cubic-magnitude / linear-angle pair
factor retains the explicit fraction `kappa^3 * delta / 16`.

This is the scalar floor used by the human pair-defect continuity argument. -/
theorem weighted_pair_floor_from_component_floors
    {kappa delta a b gap : ℝ}
    (hkappa : 0 ≤ kappa)
    (hdelta : 0 ≤ delta)
    (ha : kappa / 2 ≤ a)
    (hb : kappa / 2 ≤ b)
    (hgap : delta / 2 ≤ gap) :
    kappa ^ 3 * delta / 16 ≤ a ^ 2 * b * gap := by
  have hk2 : 0 ≤ kappa / 2 := by positivity
  have hd2 : 0 ≤ delta / 2 := by positivity
  have ha0 : 0 ≤ a := le_trans hk2 ha
  have hb0 : 0 ≤ b := le_trans hk2 hb
  have hg0 : 0 ≤ gap := le_trans hd2 hgap
  calc
    kappa ^ 3 * delta / 16 = (kappa / 2) ^ 2 * (kappa / 2) * (delta / 2) := by ring
    _ ≤ a ^ 2 * b * gap := by
      gcongr

/-- Combined finite endpoint: two half-magnitude errors and two quarter-direction
errors preserve a strictly positive weighted pair contribution whenever the
unfiltered lower bounds are nonnegative. -/
theorem filtered_weighted_pair_floor
    {kappa delta rawA rawB filteredA filteredB rawGap filteredGap err₁ err₂ : ℝ}
    (hkappa : 0 ≤ kappa)
    (hdelta : 0 ≤ delta)
    (hrawA : kappa ≤ rawA)
    (hrawB : kappa ≤ rawB)
    (hAerr : |filteredA - rawA| ≤ kappa / 2)
    (hBerr : |filteredB - rawB| ≤ kappa / 2)
    (hrawGap : delta ≤ rawGap)
    (hbudget₁ : err₁ ≤ delta / 4)
    (hbudget₂ : err₂ ≤ delta / 4)
    (htransfer : rawGap - err₁ - err₂ ≤ filteredGap) :
    kappa ^ 3 * delta / 16 ≤ filteredA ^ 2 * filteredB * filteredGap := by
  have hAf : kappa / 2 ≤ filteredA :=
    magnitude_floor_after_half_error hrawA hAerr
  have hBf : kappa / 2 ≤ filteredB :=
    magnitude_floor_after_half_error hrawB hBerr
  have hgf : delta / 2 ≤ filteredGap :=
    direction_gap_survives_two_quarter_errors
      hrawGap hbudget₁ hbudget₂ htransfer
  exact weighted_pair_floor_from_component_floors hkappa hdelta hAf hBf hgf

#print axioms magnitude_floor_after_half_error
#print axioms direction_gap_survives_two_quarter_errors
#print axioms weighted_pair_floor_from_component_floors
#print axioms filtered_weighted_pair_floor

end NSYuActiveEndpointStability
