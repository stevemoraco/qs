import Mathlib

/-!
# Pineau–Vicol low-vorticity-cut variance firewall

Finite real algebra only.

The intended PDE use is external: if a Type-I normalized vorticity field has a
positive-measure high component and a positive-measure low component, a scalar
projection of the vorticity has a nonzero two-cluster variance. Poincare can
then convert that variance into a gradient-energy lower bound. This file proves
only the finite weighted variance identities and gap arithmetic; it does not
formalize Poincare, Pineau–Vicol, Yu, vorticity, Navier–Stokes, or a Clay claim.
-/

namespace NSPVLowVortCutVariance

/-- Exact weighted two-point variance decomposition around an arbitrary center. -/
theorem weighted_two_cluster_identity
    (mHigh mLow high low center : ℝ)
    (hden : mHigh + mLow ≠ 0) :
    mHigh * (high - center)^2 + mLow * (low - center)^2 =
      (mHigh + mLow) *
          (center - (mHigh * high + mLow * low) / (mHigh + mLow))^2 +
        (mHigh * mLow / (mHigh + mLow)) * (high - low)^2 := by
  field_simp [hden]
  ring

/-- Positive cluster weights force a center-independent variance floor. -/
theorem weighted_two_cluster_floor
    (mHigh mLow high low center : ℝ)
    (hmHigh : 0 < mHigh) (hmLow : 0 < mLow) :
    (mHigh * mLow / (mHigh + mLow)) * (high - low)^2 ≤
      mHigh * (high - center)^2 + mLow * (low - center)^2 := by
  have hsum : 0 < mHigh + mLow := add_pos hmHigh hmLow
  have hden : mHigh + mLow ≠ 0 := ne_of_gt hsum
  rw [weighted_two_cluster_identity mHigh mLow high low center hden]
  have hsq :
      0 ≤ (mHigh + mLow) *
        (center - (mHigh * high + mLow * low) / (mHigh + mLow))^2 := by
    exact mul_nonneg (le_of_lt hsum) (sq_nonneg _)
  linarith

/-- Any certified scalar gap can be inserted into the weighted variance floor. -/
theorem weighted_gap_floor
    (mHigh mLow high low center gap : ℝ)
    (hmHigh : 0 < mHigh) (hmLow : 0 < mLow)
    (hgap0 : 0 ≤ gap) (hgap : gap ≤ high - low) :
    (mHigh * mLow / (mHigh + mLow)) * gap^2 ≤
      mHigh * (high - center)^2 + mLow * (low - center)^2 := by
  have hsum : 0 < mHigh + mLow := add_pos hmHigh hmLow
  have hcoeff : 0 ≤ mHigh * mLow / (mHigh + mLow) := by
    exact div_nonneg (mul_nonneg (le_of_lt hmHigh) (le_of_lt hmLow)) (le_of_lt hsum)
  have hsquare : gap^2 ≤ (high - low)^2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare hcoeff
  exact hmul.trans (weighted_two_cluster_floor mHigh mLow high low center hmHigh hmLow)

/-- The concrete gap used by the Type-I coherent-anchor / low-vorticity split. -/
theorem pv_anchor_low_gap
    (kappa high low : ℝ)
    (hHigh : 21 * kappa / 32 ≤ high)
    (hLow : low ≤ kappa / 4) :
    13 * kappa / 32 ≤ high - low := by
  linarith

#print axioms weighted_two_cluster_identity
#print axioms weighted_two_cluster_floor
#print axioms weighted_gap_floor
#print axioms pv_anchor_low_gap

end NSPVLowVortCutVariance
