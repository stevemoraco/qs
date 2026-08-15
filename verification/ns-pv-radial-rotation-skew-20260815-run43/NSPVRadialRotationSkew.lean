import Mathlib

/-!
# Pineau–Vicol rotation-skew finite firewall

Finite Euclidean algebra only.  This file does **not** formalize weighted
integrals, `SO(3)`, Pineau–Vicol, Yu, Shahmurov, Navier–Stokes, or any
Millennium statement.

The intended PDE shadow is that the infinitesimal rigid-rotation generator is
skew for radial quadratic energies.  Here we retain only the algebraic pieces
that materially prevent a false coercive inference from a skew symmetry mode.
-/

namespace NSPVRadialRotationSkew

/-- The cross-product / skew-generator form is pointwise orthogonal to the
state.  `(a,b,c)` is the rotation-axis vector and `(x,y,z)` the state. -/
theorem rotation_generator_dot_zero
    (a b c x y z : ℝ) :
    x * (b * z - c * y) +
      y * (c * x - a * z) +
      z * (a * y - b * x) = 0 := by
  ring

/-- A common infinitesimal rigid rotation is also orthogonal to the relative
state of two points. -/
theorem common_rotation_relative_dot_zero
    (a b c x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    (x₁ - x₂) * (b * (z₁ - z₂) - c * (y₁ - y₂)) +
      (y₁ - y₂) * (c * (x₁ - x₂) - a * (z₁ - z₂)) +
      (z₁ - z₂) * (a * (y₁ - y₂) - b * (x₁ - x₂)) = 0 := by
  ring

/-- Concrete unit-speed rotation about `e₃`: the instantaneous velocity is
nonzero even though its quadratic-energy pairing with the state is zero. -/
theorem e3_rotation_positive_speed_zero_energy_pairing :
    ((1 : ℝ) * 0 + 0 * 1 + 0 * 0 = 0) ∧
      ((0 : ℝ)^2 + 1^2 + 0^2 = 1) := by
  norm_num

/-- Therefore no strictly positive scalar coercivity constant can bound this
rotation speed by the absolute quadratic-energy pairing in the concrete model. -/
theorem e3_rotation_defeats_positive_pairing_coercivity
    (c : ℝ) (hc : 0 < c) :
    ¬ c * ((0 : ℝ)^2 + 1^2 + 0^2) ≤
      |(1 : ℝ) * 0 + 0 * 1 + 0 * 0| := by
  norm_num
  exact hc

/-- If a drift is decomposed into an orthogonal shape part and rotation part,
its squared size splits exactly.  This is the finite least-squares shadow of
quotienting a symmetry tangent space. -/
theorem orthogonal_shape_rotation_pythagoras
    (s₁ s₂ s₃ r₁ r₂ r₃ : ℝ)
    (horth : s₁ * r₁ + s₂ * r₂ + s₃ * r₃ = 0) :
    (s₁ + r₁)^2 + (s₂ + r₂)^2 + (s₃ + r₃)^2 =
      (s₁^2 + s₂^2 + s₃^2) + (r₁^2 + r₂^2 + r₃^2) := by
  nlinarith

#print axioms rotation_generator_dot_zero
#print axioms common_rotation_relative_dot_zero
#print axioms e3_rotation_positive_speed_zero_energy_pairing
#print axioms e3_rotation_defeats_positive_pairing_coercivity
#print axioms orthogonal_shape_rotation_pythagoras

end NSPVRadialRotationSkew
