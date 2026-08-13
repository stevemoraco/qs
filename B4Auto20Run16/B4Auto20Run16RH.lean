import Mathlib
namespace B4Auto20Run16

theorem rh_corrected_cocycle
    (Aprev A Hprev H w wnext S Cprev C : ℝ)
    (hA : A - Aprev = w * (H - Hprev) + S)
    (hCprev : Cprev = Aprev - w * Hprev)
    (hC : C = A - wnext * H) :
    C - Cprev = S + (w - wnext) * H := by
  linarith

theorem rh_positive_slack_decreasing_weight_can_still_drift_negative :
    (0 : ℝ) < 1 ∧ (1 / 2 : ℝ) < 1 ∧
      1 + (1 - (1 / 2 : ℝ)) * (-4) < 0 := by
  norm_num

theorem rh_slack_pays_adverse_history
    (w wnext H S : ℝ)
    (hpay : (w - wnext) * (-H) ≤ S) :
    0 ≤ S + (w - wnext) * H := by
  linarith

#print axioms B4Auto20Run16.rh_corrected_cocycle
#print axioms B4Auto20Run16.rh_positive_slack_decreasing_weight_can_still_drift_negative
#print axioms B4Auto20Run16.rh_slack_pays_adverse_history
end B4Auto20Run16
