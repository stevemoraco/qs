import Mathlib
namespace B4Auto20Run16

theorem bsd_component_defect_decomposition (total away component : ℕ)
    (h : total = away + component) : total - away = component := by
  omega

theorem bsd_ignoring_positive_component_undercounts (away component : ℕ)
    (hc : 0 < component) : away < away + component := by
  omega

theorem bsd_total_equals_away_iff_component_zero (total away component : ℕ)
    (h : total = away + component) : total = away ↔ component = 0 := by
  omega

#print axioms B4Auto20Run16.bsd_component_defect_decomposition
#print axioms B4Auto20Run16.bsd_ignoring_positive_component_undercounts
#print axioms B4Auto20Run16.bsd_total_equals_away_iff_component_zero
end B4Auto20Run16
