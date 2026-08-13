import Mathlib

namespace NSRealTriadSharpCurve

/-- Under the normalized real-triad pressure-cancellation equations,
    the two exterior coordinates have equal squared magnitude. -/
theorem squared_exterior_coordinates_equal
    {a b c d : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hc : a * d + b * c = 0) :
    a ^ 2 = b ^ 2 := by
  have had : a * d = -(b * c) := by
    linarith
  have hprod : a ^ 2 * d ^ 2 = b ^ 2 * c ^ 2 := by
    calc
      a ^ 2 * d ^ 2 = (a * d) ^ 2 := by ring
      _ = (b * c) ^ 2 := by rw [had]; ring
      _ = b ^ 2 * c ^ 2 := by ring
  calc
    a ^ 2 = a ^ 2 * (b ^ 2 + d ^ 2) := by rw [hb]; ring
    _ = a ^ 2 * b ^ 2 + a ^ 2 * d ^ 2 := by ring
    _ = b ^ 2 * a ^ 2 + b ^ 2 * c ^ 2 := by rw [hprod]; ring
    _ = b ^ 2 * (a ^ 2 + c ^ 2) := by ring
    _ = b ^ 2 := by rw [ha]; ring

/-- The complementary polarization coordinates also have equal squares. -/
theorem squared_complementary_coordinates_equal
    {a b c d : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hc : a * d + b * c = 0) :
    c ^ 2 = d ^ 2 := by
  have hab := squared_exterior_coordinates_equal ha hb hc
  linarith

/-- Exact desired/exterior curve for one normalized real triad. -/
theorem exact_single_channel_curve
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hc : a * d + b * c = 0)
    (hr : r = b * c - a * d) :
    r ^ 2 = 4 * a ^ 2 * (1 - a ^ 2) := by
  have hab := squared_exterior_coordinates_equal ha hb hc
  have had : a * d = -(b * c) := by
    linarith
  have hrbc : r = 2 * (b * c) := by
    rw [hr]
    linarith
  have hc2 : c ^ 2 = 1 - a ^ 2 := by
    linarith
  calc
    r ^ 2 = (2 * (b * c)) ^ 2 := by rw [hrbc]
    _ = 4 * b ^ 2 * c ^ 2 := by ring
    _ = 4 * a ^ 2 * c ^ 2 := by rw [← hab]
    _ = 4 * a ^ 2 * (1 - a ^ 2) := by rw [hc2]

/-- If `E = a^2+b^2` is the aggregate exterior square energy, then the
    desired square is exactly `2E-E^2`. -/
theorem exact_aggregate_tradeoff
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hc : a * d + b * c = 0)
    (hr : r = b * c - a * d) :
    r ^ 2 =
      2 * (a ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2) ^ 2 := by
  have hab := squared_exterior_coordinates_equal ha hb hc
  calc
    r ^ 2 = 4 * a ^ 2 * (1 - a ^ 2) :=
      exact_single_channel_curve ha hb hc hr
    _ = 2 * (a ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2) ^ 2 := by
      rw [← hab]
      ring

/-- Sharp aggregate and per-channel exterior floors. -/
theorem sharp_exterior_floors
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hc : a * d + b * c = 0)
    (hr : r = b * c - a * d) :
    r ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) ∧
      r ^ 2 ≤ 4 * a ^ 2 ∧ r ^ 2 ≤ 4 * b ^ 2 := by
  have htrade := exact_aggregate_tradeoff ha hb hc hr
  have hab := squared_exterior_coordinates_equal ha hb hc
  have hs : 0 ≤ (a ^ 2 + b ^ 2) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The retained desired coefficient has squared magnitude at most one. -/
theorem desired_square_le_one
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hc : a * d + b * c = 0)
    (hr : r = b * c - a * d) :
    r ^ 2 ≤ 1 := by
  have htrade := exact_aggregate_tradeoff ha hb hc hr
  have hs : 0 ≤ (a ^ 2 + b ^ 2 - 1) ^ 2 := sq_nonneg _
  nlinarith

/-- Maximal desired coupling forces equal half-sized exterior squares. -/
theorem maximal_coupling_forces_half
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hc : a * d + b * c = 0)
    (hr : r = b * c - a * d)
    (hmax : r ^ 2 = 1) :
    a ^ 2 = (1 : ℝ) / 2 ∧ b ^ 2 = (1 : ℝ) / 2 := by
  have htrade := exact_aggregate_tradeoff ha hb hc hr
  have hab := squared_exterior_coordinates_equal ha hb hc
  have hs : 0 ≤ (a ^ 2 + b ^ 2 - 1) ^ 2 := sq_nonneg _
  constructor <;> nlinarith

#print axioms squared_exterior_coordinates_equal
#print axioms squared_complementary_coordinates_equal
#print axioms exact_single_channel_curve
#print axioms exact_aggregate_tradeoff
#print axioms sharp_exterior_floors
#print axioms desired_square_le_one
#print axioms maximal_coupling_forces_half

end NSRealTriadSharpCurve
