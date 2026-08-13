import Mathlib

/-!
Finite algebraic firewall for a normalized real isosceles interaction.

The four scalar hypotheses are the unit-normalization equations, the exact
cancellation equation for the conjugate output, and the definition of the
desired relay coefficient. The file proves only polynomial inequalities over
`ℝ`; it does not encode Fourier analysis, Leray projection, Navier--Stokes, or
singularity formation.
-/

namespace SixLaneAudit.NSRealTriadExteriorFloor

/-- Exact cancellation forces each exterior coefficient to carry at least one
quarter of the squared desired coefficient. -/
theorem each_exterior_floor
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hcancel : a * d + b * c = 0)
    (hrelay : r = b * c - a * d) :
    r ^ 2 ≤ 4 * a ^ 2 ∧ r ^ 2 ≤ 4 * b ^ 2 := by
  have hbc : b * c = -(a * d) := by
    linarith
  have had : a * d = -(b * c) := by
    linarith
  have hd : 0 ≤ 1 - d ^ 2 := by
    nlinarith [sq_nonneg b]
  have hc : 0 ≤ 1 - c ^ 2 := by
    nlinarith [sq_nonneg a]
  have hma : 0 ≤ 4 * a ^ 2 * (1 - d ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a)) hd
  have hmb : 0 ≤ 4 * b ^ 2 * (1 - c ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg b)) hc
  constructor
  · rw [hrelay, hbc]
    nlinarith
  · rw [hrelay, had]
    nlinarith

/-- Aggregate squared exterior contribution. -/
theorem total_exterior_floor
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hcancel : a * d + b * c = 0)
    (hrelay : r = b * c - a * d) :
    r ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  rcases each_exterior_floor ha hb hcancel hrelay with ⟨h1, h2⟩
  nlinarith

/-- Deleting both exterior coefficients deletes the desired relay. -/
theorem zero_exteriors_force_zero_relay
    {a b c d r : ℝ}
    (ha : a ^ 2 + c ^ 2 = 1)
    (hb : b ^ 2 + d ^ 2 = 1)
    (hcancel : a * d + b * c = 0)
    (hrelay : r = b * c - a * d)
    (ha0 : a = 0)
    (hb0 : b = 0) :
    r = 0 := by
  have h := total_exterior_floor ha hb hcancel hrelay
  rw [ha0, hb0] at h
  nlinarith [sq_nonneg r]

#print axioms each_exterior_floor
#print axioms total_exterior_floor
#print axioms zero_exteriors_force_zero_relay

end SixLaneAudit.NSRealTriadExteriorFloor
