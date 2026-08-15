import Mathlib

/-!
# Pineau–Vicol rotation-quotient drift firewalls

Finite Euclidean/real-algebra statements only.

These lemmas formalize the elementary obstruction behind a source-level
Navier–Stokes audit: a common rigid rotation can have nonzero tangent speed
while preserving a relative pairwise direction defect.  Therefore a raw
self-similar drift cannot be identified algebraically with a relative angular
defect before quotienting or explicitly paying the rotation symmetry mode.

Nothing here formalizes the Navier–Stokes equations, the Pineau–Vicol RSS
ansatz or regularity theorem, Yu's filtered-vorticity estimates, or a
Millennium Prize statement.
-/

namespace NSPVRotationQuotientDrift

/-- The planar infinitesimal rotation `J(x,y)=(-y,x)` is orthogonal to `(x,y)`. -/
theorem skew_rotation_energy_derivative_zero (x y : ℝ) :
    2 * x * (-y) + 2 * y * x = 0 := by
  ring

/-- Infinitesimal planar rotation preserves the squared norm. -/
theorem skew_rotation_norm_sq (x y : ℝ) :
    (-y) ^ 2 + x ^ 2 = x ^ 2 + y ^ 2 := by
  ring

/-- Applying the same planar infinitesimal rotation to two points preserves
    their relative squared speed exactly. -/
theorem common_rotation_relative_speed_sq
    (x₁ y₁ x₂ y₂ : ℝ) :
    ((-y₁) - (-y₂)) ^ 2 + (x₁ - x₂) ^ 2 =
      (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  ring

/-- Two identical directions have zero relative pair defect. -/
theorem common_mode_pair_defect_zero :
    (((1 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2) = 0 := by
  norm_num

/-- The same unit direction has unit infinitesimal rotation speed. -/
theorem common_mode_rotation_speed_one :
    (-(0 : ℝ)) ^ 2 + (1 : ℝ) ^ 2 = 1 := by
  norm_num

/-- A positive common-mode rotational cost cannot be bounded by the zero
    relative defect of two identical directions. -/
theorem positive_common_rotation_not_charged_by_pair_defect
    (c : ℝ) (hc : 0 < c) :
    ¬ c * ((-(0 : ℝ)) ^ 2 + (1 : ℝ) ^ 2) ≤
      (((1 : ℝ) - 1) ^ 2 + ((0 : ℝ) - 0) ^ 2) := by
  norm_num
  exact hc

/-- If raw drift is bounded by quotient-shape drift plus rotational drift,
    and each contribution is at most half of a trigger threshold, then the raw
    drift lies below that threshold. -/
theorem quotient_plus_rotation_triggers_raw
    (raw shape rotation delta : ℝ)
    (hraw : raw ≤ shape + rotation)
    (hshape : shape ≤ delta / 2)
    (hrotation : rotation ≤ delta / 2) :
    raw ≤ delta := by
  linarith

/-- One-dimensional shadow of relative-equilibrium rigidity: if a nonzero
    orbit tangent is multiplied by two speeds and produces the same autonomous
    forcing, then the speeds agree.  In a group-action application, any
    remaining ambiguity must lie in the stabilizer kernel. -/
theorem nonzero_orbit_tangent_forces_unique_speed
    (g a b forcing : ℝ)
    (hg : g ≠ 0)
    (ha : a * g = forcing)
    (hb : b * g = forcing) :
    a = b := by
  have hmul : (a - b) * g = 0 := by
    calc
      (a - b) * g = a * g - b * g := by ring
      _ = 0 := by rw [ha, hb]; ring
  have hab : a - b = 0 := (mul_eq_zero.mp hmul).resolve_right hg
  linarith

#print axioms skew_rotation_energy_derivative_zero
#print axioms skew_rotation_norm_sq
#print axioms common_rotation_relative_speed_sq
#print axioms common_mode_pair_defect_zero
#print axioms common_mode_rotation_speed_one
#print axioms positive_common_rotation_not_charged_by_pair_defect
#print axioms quotient_plus_rotation_triggers_raw
#print axioms nonzero_orbit_tangent_forces_unique_speed

end NSPVRotationQuotientDrift
