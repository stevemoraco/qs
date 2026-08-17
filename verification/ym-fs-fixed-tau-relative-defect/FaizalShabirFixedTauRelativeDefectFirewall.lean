import Mathlib

namespace Millennium.YangMills.FaizalShabirFixedTauRelativeDefectFirewall

theorem gapped_radius_makes_relative_loss_strictly_larger
    (r eps : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_one : r < 1)
    (heps : 0 < eps) :
    eps < eps / r := by
  apply (lt_div_iff₀ hr_pos).2
  nlinarith

theorem unit_coefficient_pays_relative_loss_only_at_radius_ge_one
    (r eps : ℝ)
    (hr_pos : 0 < r)
    (heps : 0 < eps)
    (hpay : eps / r ≤ eps) :
    1 ≤ r := by
  have hmul : eps ≤ eps * r := (div_le_iff₀ hr_pos).mp hpay
  nlinarith

theorem fixed_tau_target_radius_budget
    (r eps rNext rTarget : ℝ)
    (hnext : rNext ≤ r + eps)
    (hbudget : eps ≤ rTarget - r) :
    rNext ≤ rTarget := by
  linarith

theorem relative_defect_gives_multiplicative_radius_bound
    (r eps theta : ℝ)
    (hbudget : eps ≤ theta * r) :
    r + eps ≤ (1 + theta) * r := by
  linarith

theorem fixed_tau_relative_defect_consumer
    (r eps rNext theta : ℝ)
    (hnext : rNext ≤ r + eps)
    (hbudget : eps ≤ theta * r) :
    rNext ≤ (1 + theta) * r := by
  exact hnext.trans (relative_defect_gives_multiplicative_radius_bound r eps theta hbudget)

#print axioms gapped_radius_makes_relative_loss_strictly_larger
#print axioms unit_coefficient_pays_relative_loss_only_at_radius_ge_one
#print axioms fixed_tau_target_radius_budget
#print axioms relative_defect_gives_multiplicative_radius_bound
#print axioms fixed_tau_relative_defect_consumer

end Millennium.YangMills.FaizalShabirFixedTauRelativeDefectFirewall
