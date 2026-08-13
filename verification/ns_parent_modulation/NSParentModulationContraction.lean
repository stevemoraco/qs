import Mathlib

namespace NSParentModulationContraction

/-- After exact tangent-Beltrami cancellation, a coefficient modulation at the
parent carrier scale has exponent
`1 + (alpha-1) - beta - b*(alpha-beta)`.
This is exactly the negative product of the two strict interior gaps. -/
theorem parent_modulation_exponent_factorization
    (alpha beta b : ℚ) :
    1 + (alpha - 1) - beta - b * (alpha - beta) =
      -(b - 1) * (alpha - beta) := by
  ring

/-- Every strict Palasek interior point `1 < b` and `beta < alpha` gives a
strictly negative parent-modulation contraction exponent. -/
theorem parent_modulation_is_strictly_contracting
    (alpha beta b : ℚ)
    (hb : 1 < b)
    (hbeta : beta < alpha) :
    -(b - 1) * (alpha - beta) < 0 := by
  have h1 : 0 < b - 1 := sub_pos.mpr hb
  have h2 : 0 < alpha - beta := sub_pos.mpr hbeta
  nlinarith [mul_pos h1 h2]

/-- Exact corrected exponent at the live rational point
`alpha=9/4`, `b=17/16`, `beta=35/16`. -/
theorem alpha_nine_four_parent_modulation_exponent :
    (1 : ℚ) + ((9 : ℚ) / 4 - 1) - (35 : ℚ) / 16 -
        ((17 : ℚ) / 16) * ((9 : ℚ) / 4 - (35 : ℚ) / 16) =
      -(1 : ℚ) / 256 := by
  norm_num

/-- The earlier micro-envelope estimate is stronger, but it is not the
correct worst case when the DLS coefficient maps inherit the parent carrier. -/
theorem alpha_nine_four_micro_envelope_exponent :
    -(35 : ℚ) / 16 + (5 : ℚ) / 6 + ((9 : ℚ) / 4 - 1) -
        ((17 : ℚ) / 16) * ((9 : ℚ) / 4 - (35 : ℚ) / 16) =
      -(131 : ℚ) / 768 := by
  norm_num

/-- An aggregate finite-depth cost budget of `N^(1/1024)` leaves a strict
`N^(-3/1024)` contraction at the corrected master bottleneck. -/
theorem aggregate_cost_budget_leaves_margin :
    -(1 : ℚ) / 256 + (1 : ℚ) / 1024 = -(3 : ℚ) / 1024 := by
  norm_num

/-- A proposed `N^(1/64)` adaptive-depth cost budget overwhelms the corrected
`N^(-1/256)` contraction and therefore cannot be inserted silently. -/
theorem one_over_sixty_four_budget_breaks_margin :
    -(1 : ℚ) / 256 + (1 : ℚ) / 64 = (3 : ℚ) / 256 := by
  norm_num

#print axioms parent_modulation_exponent_factorization
#print axioms parent_modulation_is_strictly_contracting
#print axioms alpha_nine_four_parent_modulation_exponent
#print axioms alpha_nine_four_micro_envelope_exponent
#print axioms aggregate_cost_budget_leaves_margin
#print axioms one_over_sixty_four_budget_breaks_margin

end NSParentModulationContraction
