import Mathlib

/-!
# Golay carrier return: finite algebraic and scaling core

This file formalizes only:

* exact additive return identities for a cross Fourier mode and its parents;
* the rational parametrization identity for one circle;
* equal-shell consequences of two points on that circle;
* the planar lower contribution to a cross-frequency norm;
* an exact family where `N * theta` dominates `r` but `N * theta^2 = r`;
* the corrected quadratic separation condition for the scalar return gain; and
* the elementary viscous-slaving parent-return estimate.

It does not formalize helical Fourier polarization, the Navier--Stokes bilinear
operator, Golay arrays, nonlinear shadowing, or finite-time breakdown.
-/

namespace NSGolayCarrierReturn

/-- A cross mode `C-D` returns exactly to its first parent after interaction
with the second parent frequency. -/
theorem cross_mode_returns_to_first
    {G : Type*} [AddCommGroup G] (C D : G) :
    (C - D) + D = C := by
  abel

/-- The negative cross mode returns exactly to the second parent after
interaction with the first parent frequency. -/
theorem neg_cross_mode_returns_to_second
    {G : Type*} [AddCommGroup G] (C D : G) :
    -(C - D) + C = D := by
  abel

/-- Rational parametrization of the unit circle. -/
theorem rational_circle_identity (t : ℝ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 +
        ((2 * t) / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  field_simp [hden]
  ring

/-- Two planar points on one circle give equal three-dimensional shell
radii after the same vertical coordinate is added; subtracting the same
vertical lower frequency also preserves the second common shell. -/
theorem common_circle_gives_two_common_shells
    (x₁ y₁ x₂ y₂ L z r : ℝ)
    (h₁ : x₁ ^ 2 + y₁ ^ 2 = L ^ 2)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 = L ^ 2) :
    (x₁ ^ 2 + y₁ ^ 2 + z ^ 2 =
        x₂ ^ 2 + y₂ ^ 2 + z ^ 2) ∧
      (x₁ ^ 2 + y₁ ^ 2 + (z - r) ^ 2 =
        x₂ ^ 2 + y₂ ^ 2 + (z - r) ^ 2) := by
  constructor <;> nlinarith

/-- The squared norm of a three-dimensional cross frequency dominates the
squared norm of its planar separation. -/
theorem cross_frequency_sq_dominates_planar
    (dx dy r : ℝ) :
    dx ^ 2 + dy ^ 2 ≤ dx ^ 2 + dy ^ 2 + r ^ 2 := by
  nlinarith [sq_nonneg r]

/-- CRITIC: arbitrarily strong linear separation `N*theta >> r` does not
force the quadratic return scale `N*theta^2` to dominate `r`.

For `N=m^4`, `r=m^2`, and `theta=m⁻¹`, the linear ratio grows like `m`,
while the quadratic scale is exactly equal to `r`. -/
theorem linear_separation_can_miss_quadratic_gate
    (m : ℝ) (hm : 1 < m) :
    let N := m ^ 4
    let r := m ^ 2
    let theta := m⁻¹
    r < N * theta ∧ N * theta ^ 2 = r := by
  dsimp
  have hmpos : 0 < m := lt_trans zero_lt_one hm
  have hm0 : m ≠ 0 := ne_of_gt hmpos
  have hlinear : m ^ 4 * m⁻¹ = m ^ 3 := by
    field_simp [hm0]
  have hquadratic : m ^ 4 * (m⁻¹) ^ 2 = m ^ 2 := by
    field_simp [hm0]
  rw [hlinear, hquadratic]
  constructor
  · have hpos : 0 < m ^ 2 * (m - 1) :=
      mul_pos (sq_pos_of_pos hmpos) (sub_pos.mpr hm)
    nlinarith
  · rfl

/-- In the same family, the normalized scalar return gain is exactly one
when viscosity is normalized to one. -/
theorem linear_separation_family_has_unit_return_gain
    (m : ℝ) (hm : 1 < m) :
    let N := m ^ 4
    let r := m ^ 2
    let theta := m⁻¹
    r / (N * theta ^ 2) = 1 := by
  dsimp
  have hm0 : m ≠ 0 := by
    nlinarith
  field_simp [hm0]

/-- CLEANER: the corrected quadratic separation budget is exactly what is
needed to bound the normalized scalar return gain. -/
theorem quadratic_separation_controls_loop_gain
    (N r theta nu epsilon : ℝ)
    (hN : 0 < N) (htheta : 0 < theta) (hnu : 0 < nu)
    (hsep : r ≤ epsilon * (nu * N * theta ^ 2)) :
    r / (nu * N * theta ^ 2) ≤ epsilon := by
  have hden : 0 < nu * N * theta ^ 2 := by
    positivity
  exact (div_le_iff₀ hden).2 hsep

/-- The corrected scalar gate is an equivalence, not merely a sufficient
condition. -/
theorem loop_gain_le_iff_quadratic_separation
    (N r theta nu epsilon : ℝ)
    (hN : 0 < N) (htheta : 0 < theta) (hnu : 0 < nu) :
    r / (nu * N * theta ^ 2) ≤ epsilon ↔
      r ≤ epsilon * (nu * N * theta ^ 2) := by
  have hden : 0 < nu * N * theta ^ 2 := by
    positivity
  exact div_le_iff₀ hden

/-- If a cross mode is slaved at frequency `N*theta`, multiplying its
amplitude by one parent derivative `N` yields the sharper return scale
`r/(nu*N*theta^2)`. -/
theorem slaved_cross_mode_parent_return_bound
    (N r theta nu X : ℝ)
    (hN : 0 < N) (htheta : 0 < theta) (hnu : 0 < nu)
    (hX : X ≤ r / (nu * (N * theta) ^ 2)) :
    N * X ≤ r / (nu * N * theta ^ 2) := by
  have hNnonneg : 0 ≤ N := le_of_lt hN
  calc
    N * X ≤ N * (r / (nu * (N * theta) ^ 2)) :=
      mul_le_mul_of_nonneg_left hX hNnonneg
    _ = r / (nu * N * theta ^ 2) := by
      field_simp [ne_of_gt hN, ne_of_gt htheta, ne_of_gt hnu]

#print axioms cross_mode_returns_to_first
#print axioms neg_cross_mode_returns_to_second
#print axioms rational_circle_identity
#print axioms common_circle_gives_two_common_shells
#print axioms cross_frequency_sq_dominates_planar
#print axioms linear_separation_can_miss_quadratic_gate
#print axioms linear_separation_family_has_unit_return_gain
#print axioms quadratic_separation_controls_loop_gain
#print axioms loop_gain_le_iff_quadratic_separation
#print axioms slaved_cross_mode_parent_return_bound

end NSGolayCarrierReturn
