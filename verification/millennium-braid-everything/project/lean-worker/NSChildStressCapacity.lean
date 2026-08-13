import Mathlib

namespace NSChildStressCapacity

/-- Exact algebra for the exponent gap between Palasek's child high-high
stress capacity and the parent viscous scale. -/
theorem exponent_gap_identity (α β b : ℝ) :
    (α + 2 * b * (β - α)) - (β - α + 2)
      = (2 * b - 1) * β - 2 * (b - 1) * α - 2 := by
  ring

/-- At the lower endpoint `β=2b`, the gap factors exactly. -/
theorem lower_endpoint_gap_factor (α b : ℝ) :
    (2 * b - 1) * (2 * b) - 2 * (b - 1) * α - 2
      = 2 * (b - 1) * (2 * b + 1 - α) := by
  ring

/-- In the physical Palasek window, strict `β>2b` leaves a strictly positive
power gap. No PDE semantics are asserted here. -/
theorem child_stress_gap_pos
    {α β b : ℝ}
    (hb : 1 < b)
    (hβ : 2 * b < β)
    (hα : α ≤ 5 / 2) :
    0 < (2 * b - 1) * β - 2 * (b - 1) * α - 2 := by
  have hcoef : 0 < 2 * b - 1 := by linarith
  have hmono :
      (2 * b - 1) * (2 * b) < (2 * b - 1) * β :=
    mul_lt_mul_of_pos_left hβ hcoef
  have hsep : 0 < 2 * b + 1 - α := by linarith
  have hfact : 0 < 2 * (b - 1) * (2 * b + 1 - α) := by positivity
  have hid := lower_endpoint_gap_factor α b
  nlinarith

/-- The result remains true under the slightly more general condition
`α < 2b+1`, exposing the exact geometric requirement. -/
theorem child_stress_gap_pos_general
    {α β b : ℝ}
    (hb : 1 < b)
    (hβ : 2 * b < β)
    (hα : α < 2 * b + 1) :
    0 < (2 * b - 1) * β - 2 * (b - 1) * α - 2 := by
  have hcoef : 0 < 2 * b - 1 := by linarith
  have hmono :
      (2 * b - 1) * (2 * b) < (2 * b - 1) * β :=
    mul_lt_mul_of_pos_left hβ hcoef
  have hfact : 0 < 2 * (b - 1) * (2 * b + 1 - α) := by positivity
  have hid := lower_endpoint_gap_factor α b
  nlinarith

#print axioms exponent_gap_identity
#print axioms lower_endpoint_gap_factor
#print axioms child_stress_gap_pos
#print axioms child_stress_gap_pos_general

end NSChildStressCapacity
