import Mathlib

/-!
# Two-cell outer canceller: finite algebra

This file formalizes denominator-cleared integer carrier identities, the
exceptional `C=3` two-cell closure identities, and the scalar cross-channel
no-go. It does not formalize Fourier series, Leray projection, root-of-unity
classification, localization, Navier--Stokes solutions, or blowup.
-/

namespace NSBraid
namespace TwoCellOuterCanceller

abbrev Vec3 := ℤ × ℤ × ℤ

@[simp] def add : Vec3 → Vec3 → Vec3
  | (x₁, x₂, x₃), (y₁, y₂, y₃) => (x₁ + y₁, x₂ + y₂, x₃ + y₃)

@[simp] def neg : Vec3 → Vec3
  | (x, y, z) => (-x, -y, -z)

@[simp] def scale (a : ℤ) : Vec3 → Vec3
  | (x, y, z) => (a * x, a * y, a * z)

@[simp] def dot : Vec3 → Vec3 → ℤ
  | (x₁, x₂, x₃), (y₁, y₂, y₃) => x₁ * y₁ + x₂ * y₂ + x₃ * y₃

@[simp] def normSq (x : Vec3) : ℤ := dot x x

@[simp] def cross : Vec3 → Vec3 → Vec3
  | (x₁, x₂, x₃), (y₁, y₂, y₃) =>
      (x₂ * y₃ - x₃ * y₂,
       x₃ * y₁ - x₁ * y₃,
       x₁ * y₂ - x₂ * y₁)

@[simp] def D (C : ℤ) : ℤ := 9 + C ^ 2

@[simp] def ell0 (C : ℤ) : Vec3 := (D C, 0, 0)
@[simp] def h0 (C : ℤ) : Vec3 := (0, C * D C, 0)
@[simp] def ell1 (C : ℤ) : Vec3 := (9 - C ^ 2, 6 * C, 0)
@[simp] def h1 (C : ℤ) : Vec3 := (-6 * C ^ 2, C * (9 - C ^ 2), 0)

/-- The two lower half-carriers have exactly equal length. -/
theorem lower_norm_equal (C : ℤ) :
    normSq (ell1 C) = normSq (ell0 C) := by
  simp
  ring

/-- The two auxiliary carriers have exactly equal length. -/
theorem auxiliary_norm_equal (C : ℤ) :
    normSq (h1 C) = normSq (h0 C) := by
  simp
  ring

/-- Both cells are orthogonal carrier pairs. -/
theorem first_cell_orthogonal (C : ℤ) : dot (ell0 C) (h0 C) = 0 := by
  simp

/-- Both cells are orthogonal carrier pairs. -/
theorem second_cell_orthogonal (C : ℤ) : dot (ell1 C) (h1 C) = 0 := by
  simp
  ring

/-- The two cells have exactly the same desired output polarization. -/
theorem desired_polarization_equal (C : ℤ) :
    cross (ell1 C) (h1 C) = cross (ell0 C) (h0 C) := by
  ext <;> simp <;> ring

/-- One positive outer sideband of the first cell exactly matches one negative
branch outer sideband of the second cell for every integer ratio. -/
theorem first_outer_frequency_match (C : ℤ) :
    add (scale 3 (ell0 C)) (h0 C) =
      add (scale 3 (ell1 C)) (neg (h1 C)) := by
  ext <;> simp <;> ring

/-- At the exceptional ratio `C=3`, the remaining outer frequencies are
reality conjugates. -/
theorem second_outer_conjugate_match :
    add (scale 3 (ell0 3)) (neg (h0 3)) =
      neg (add (scale 3 (ell1 3)) (h1 3)) := by
  norm_num

/-- The exact two low carriers in the exceptional square. -/
theorem exceptional_low_carriers :
    scale 2 (ell0 3) = (36, 0, 0) ∧
      scale 2 (ell1 3) = (0, 36, 0) := by
  constructor <;> norm_num

/-- The four exact positive high carriers in the exceptional square. -/
theorem exceptional_high_carriers :
    add (ell0 3) (h0 3) = (18, 54, 0) ∧
    add (ell0 3) (neg (h0 3)) = (18, -54, 0) ∧
    add (ell1 3) (h1 3) = (-54, 18, 0) ∧
    add (ell1 3) (neg (h1 3)) = (54, 18, 0) := by
  norm_num

/-- Same-branch cross output factor. -/
def sameFactor (C : ℝ) : ℝ :=
  -6 * C ^ 3 * (C ^ 2 + 1) * (C ^ 2 + 9) ^ 5

/-- Mixed-branch cross output factor. -/
def mixedFactor (C : ℝ) : ℝ :=
  4 * C ^ 3 * (C ^ 2 + 3) * (C ^ 2 + 9) ^ 5

/-- The same-branch factor is nonzero at every nonzero ratio. -/
theorem sameFactor_ne_zero (C : ℝ) (hC : C ≠ 0) :
    sameFactor C ≠ 0 := by
  have hC3 : C ^ 3 ≠ 0 := pow_ne_zero 3 hC
  have h1 : C ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg C]
  have h9 : C ^ 2 + 9 ≠ 0 := by nlinarith [sq_nonneg C]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) hC3) h1)
    (pow_ne_zero 5 h9)

/-- The mixed-branch factor is nonzero at every nonzero ratio. -/
theorem mixedFactor_ne_zero (C : ℝ) (hC : C ≠ 0) :
    mixedFactor C ≠ 0 := by
  have hC3 : C ^ 3 ≠ 0 := pow_ne_zero 3 hC
  have h3 : C ^ 2 + 3 ≠ 0 := by nlinarith [sq_nonneg C]
  have h9 : C ^ 2 + 9 ≠ 0 := by nlinarith [sq_nonneg C]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) hC3) h3)
    (pow_ne_zero 5 h9)

/-- Exact scalar no-go: vanishing of one same-branch and one mixed-branch
cross-channel coefficient forces both desired-output parameters to vanish. -/
theorem cross_channel_no_exact_closure
    (C z0 z1 : ℝ) (hC : C ≠ 0)
    (hsame : sameFactor C * (z0 - z1) = 0)
    (hmixed : mixedFactor C * (z0 + z1) = 0) :
    z0 = 0 ∧ z1 = 0 := by
  have hzminus : z0 - z1 = 0 :=
    (mul_eq_zero.mp hsame).resolve_left (sameFactor_ne_zero C hC)
  have hzplus : z0 + z1 = 0 :=
    (mul_eq_zero.mp hmixed).resolve_left (mixedFactor_ne_zero C hC)
  constructor <;> linarith

/-- With equal desired parameters, the two exceptional mixed output
frequencies are exactly the displayed diagonal vectors. -/
theorem exceptional_mixed_frequencies :
    add (add (ell0 3) (h0 3)) (add (ell1 3) (neg (h1 3))) =
        (72, 72, 0) ∧
      add (add (ell0 3) (neg (h0 3))) (add (ell1 3) (h1 3)) =
        (-36, -36, 0) := by
  constructor <;> norm_num

#print axioms lower_norm_equal
#print axioms auxiliary_norm_equal
#print axioms first_cell_orthogonal
#print axioms second_cell_orthogonal
#print axioms desired_polarization_equal
#print axioms first_outer_frequency_match
#print axioms second_outer_conjugate_match
#print axioms exceptional_low_carriers
#print axioms exceptional_high_carriers
#print axioms sameFactor_ne_zero
#print axioms mixedFactor_ne_zero
#print axioms cross_channel_no_exact_closure
#print axioms exceptional_mixed_frequencies

end TwoCellOuterCanceller
end NSBraid
