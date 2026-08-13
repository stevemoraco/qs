import Mathlib

namespace NSFloquetWakeupWindow

/-- The three strict inequalities needed for a polynomial number `N^eps` of
Floquet cycles: WKB accumulation, total viscous attenuation, and residence
inside the parent stability plateau. -/
theorem wakeup_window_gives_three_negative_exponents
    (eps b beta : ℚ)
    (hWKB : eps < b - 1)
    (hVisc : eps < beta - 2 * b)
    (hPlateau : eps < beta * (1 - 1 / b)) :
    eps - (b - 1) < 0 ∧
      eps + 2 * b - beta < 0 ∧
      eps - beta * (1 - 1 / b) < 0 := by
  constructor
  · linarith
  constructor <;> linarith

/-- The parent-to-previous-parent growth-rate ratio has exponent
`beta*(1-1/b) = beta*(b-1)/b`. -/
theorem plateau_ratio_exponent_factorization
    (b beta : ℚ) (hb : b ≠ 0) :
    beta * (1 - 1 / b) = beta * (b - 1) / b := by
  field_simp [hb]
  ring

/-- At the live point, the relative child carrier is `N^(1/16)`. -/
theorem live_relative_carrier_exponent :
    (17 : ℚ) / 16 - 1 = (1 : ℚ) / 16 := by
  norm_num

/-- At the live point, the one-cycle dimensionless viscous exponent is also
`-1/16`. -/
theorem live_one_cycle_viscous_exponent :
    2 * ((17 : ℚ) / 16) - (35 : ℚ) / 16 = -(1 : ℚ) / 16 := by
  norm_num

/-- Choosing `eps=1/64` makes the number of cycles the fourth root of the
relative carrier parameter. -/
theorem live_cycle_count_is_quarter_power_of_relative_carrier :
    (1 : ℚ) / 64 =
      (1 : ℚ) / 4 * (((17 : ℚ) / 16) - 1) := by
  norm_num

/-- The cumulative WKB defect exponent is strictly negative. -/
theorem live_cumulative_wkb_exponent :
    (1 : ℚ) / 64 - (((17 : ℚ) / 16) - 1) =
      -(3 : ℚ) / 64 := by
  norm_num

/-- The cumulative viscous attenuation exponent is the same strict margin. -/
theorem live_cumulative_viscous_exponent :
    (1 : ℚ) / 64 + 2 * ((17 : ℚ) / 16) - (35 : ℚ) / 16 =
      -(3 : ℚ) / 64 := by
  norm_num

/-- The polynomial wakeup time is also far inside the parent stability
plateau. -/
theorem live_parent_plateau_exponent :
    (1 : ℚ) / 64 -
        ((35 : ℚ) / 16) * (1 - 1 / ((17 : ℚ) / 16)) =
      -(123 : ℚ) / 1088 := by
  norm_num

/-- The live admissible wakeup interval is nonempty; `1/64` lies below all
three strict ceilings. -/
theorem live_one_over_sixty_four_is_admissible :
    (1 : ℚ) / 64 < ((17 : ℚ) / 16) - 1 ∧
      (1 : ℚ) / 64 < (35 : ℚ) / 16 - 2 * ((17 : ℚ) / 16) ∧
      (1 : ℚ) / 64 <
        ((35 : ℚ) / 16) * (1 - 1 / ((17 : ℚ) / 16)) := by
  norm_num

#print axioms wakeup_window_gives_three_negative_exponents
#print axioms plateau_ratio_exponent_factorization
#print axioms live_relative_carrier_exponent
#print axioms live_one_cycle_viscous_exponent
#print axioms live_cycle_count_is_quarter_power_of_relative_carrier
#print axioms live_cumulative_wkb_exponent
#print axioms live_cumulative_viscous_exponent
#print axioms live_parent_plateau_exponent
#print axioms live_one_over_sixty_four_is_admissible

end NSFloquetWakeupWindow
