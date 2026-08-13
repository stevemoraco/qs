import Mathlib

/-!
# Six-color equal-shell high-high isolation: finite core

This file formalizes only explicit integer-vector identities and a finite
cross-color squared-radius separation.  It does not formalize Fourier series,
Leray projection, localization, Navier--Stokes solutions, an infinite cascade,
or any Clay statement.
-/

namespace NSBraid
namespace SixColorHighHighIsolation

abbrev Vec3 := ℤ × ℤ × ℤ

inductive Color
  | c0 | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq

inductive Sign
  | pos | neg
  deriving DecidableEq

@[simp] def sgn : Sign → ℤ
  | .pos => 1
  | .neg => -1

@[simp] def add : Vec3 → Vec3 → Vec3
  | (x₁, x₂, x₃), (y₁, y₂, y₃) => (x₁ + y₁, x₂ + y₂, x₃ + y₃)

@[simp] def sub : Vec3 → Vec3 → Vec3
  | (x₁, x₂, x₃), (y₁, y₂, y₃) => (x₁ - y₁, x₂ - y₂, x₃ - y₃)

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

@[simp] def q : Color → Vec3
  | .c0 => (1, 1, 0)
  | .c1 => (1, -1, 0)
  | .c2 => (1, 0, 1)
  | .c3 => (1, 0, -1)
  | .c4 => (0, 1, 1)
  | .c5 => (0, 1, -1)

@[simp] def ell : Color → Vec3
  | .c0 => (-1, 1, 14)
  | .c1 => (-7, -7, 10)
  | .c2 => (1, 14, -1)
  | .c3 => (-7, 10, -7)
  | .c4 => (-14, 1, -1)
  | .c5 => (-14, -1, -1)

@[simp] def h (i : Color) : Vec3 := scale 2 (cross (q i) (ell i))

@[simp] def g (i : Color) : Vec3 := cross (ell i) (h i)

@[simp] def carrier (i : Color) (branch : Sign) : Vec3 :=
  add (ell i) (scale (sgn branch) (h i))

@[simp] def signedCarrier (i : Color) (branch reality : Sign) : Vec3 :=
  scale (sgn reality) (carrier i branch)

@[simp] def aPol (i : Color) : Vec3 :=
  add (sub (scale 198 (h i)) (scale 1584 (ell i))) (g i)

@[simp] def bPol (i : Color) : Vec3 :=
  sub (add (scale 198 (h i)) (scale 1584 (ell i))) (g i)

@[simp] def pairOutput (u k v r : Vec3) : Vec3 :=
  add (scale (dot u r) v) (scale (dot v k) u)

/-- All six target directions have the same squared length. -/
theorem q_norm (i : Color) : normSq (q i) = 2 := by
  cases i <;> norm_num

/-- All six lower half-carriers have one common squared length. -/
theorem ell_norm (i : Color) : normSq (ell i) = 198 := by
  cases i <;> norm_num

/-- Every chosen half-carrier is perpendicular to its stress direction. -/
theorem q_ell_orthogonal (i : Color) : dot (q i) (ell i) = 0 := by
  cases i <;> norm_num

/-- Every auxiliary color has the same squared length. -/
theorem h_norm (i : Color) : normSq (h i) = 1584 := by
  cases i <;> norm_num

/-- The two directions in every cell are perpendicular. -/
theorem ell_h_orthogonal (i : Color) : dot (ell i) (h i) = 0 := by
  cases i <;> norm_num

/-- The desired output polarization is exactly the prescribed stress direction. -/
theorem cross_target (i : Color) : g i = scale 396 (q i) := by
  cases i <;> norm_num

/-- Every one of the twelve positive high carriers lies on one exact shell. -/
theorem carrier_norm (i : Color) (branch : Sign) :
    normSq (carrier i branch) = 1782 := by
  cases i <;> cases branch <;> norm_num

/-- The two branches in one color sum to the designated lower carrier. -/
theorem designated_sum (i : Color) :
    add (carrier i .pos) (carrier i .neg) = scale 2 (ell i) := by
  cases i <;> norm_num

/-- The first integer polarization is exactly transverse. -/
theorem a_transverse (i : Color) :
    dot (aPol i) (carrier i .pos) = 0 := by
  cases i <;> norm_num

/-- The second integer polarization is exactly transverse. -/
theorem b_transverse (i : Color) :
    dot (bPol i) (carrier i .neg) = 0 := by
  cases i <;> norm_num

/-- The same-color desired output is a frequency-parallel gradient plus one
nonzero multiple of the prescribed stress direction. -/
theorem desired_output_decomposition (i : Color) :
    pairOutput (aPol i) (carrier i .pos) (bPol i) (carrier i .neg) =
      add (scale (-4 * 198 * 1584 * 1584) (ell i))
          (scale (4 * 198 * 1584) (g i)) := by
  cases i <;> norm_num

/-- The unavoidable real-conjugate difference output is exactly parallel to
`h`, hence to its output frequency `2h`. -/
theorem difference_output_parallel (i : Color) :
    pairOutput (aPol i) (carrier i .pos)
      (bPol i) (scale (-1) (carrier i .neg)) =
        scale (4 * 198 * 198 * 1584) (h i) := by
  cases i <;> norm_num

/-- Self-harmonics vanish before projection. -/
theorem a_self_zero (i : Color) :
    pairOutput (aPol i) (carrier i .pos) (aPol i) (carrier i .pos) =
      (0, 0, 0) := by
  cases i <;> norm_num

/-- Self-harmonics vanish before projection. -/
theorem b_self_zero (i : Color) :
    pairOutput (bPol i) (carrier i .neg) (bPol i) (carrier i .neg) =
      (0, 0, 0) := by
  cases i <;> norm_num

/-- Exact exhaustive cross-color firewall: every sum of two signed real high
carriers from distinct colors has squared radius at least `378` away from the
designated lower-shell squared radius `792`.

The proof is kernel reduction over the finite six-color/sign type.  It contains
no analytic Fourier or PDE premise.
-/
theorem cross_color_radial_gap
    (i j : Color) (hij : i ≠ j)
    (bi bj ri rj : Sign) :
    (378 : ℕ) ≤ Int.natAbs
      (normSq (add (signedCarrier i bi ri) (signedCarrier j bj rj)) - 792) := by
  cases i <;> cases j <;> cases bi <;> cases bj <;>
    cases ri <;> cases rj <;> simp_all <;> norm_num

/-- The localization exponent is strictly sublinear throughout the strict
Palasek packet window. -/
theorem localization_width_sublinear (alpha : ℝ)
    (hα : alpha < 5 / 2) :
    2 * (alpha - 1) / 3 < 1 := by
  linarith

#print axioms q_norm
#print axioms ell_norm
#print axioms q_ell_orthogonal
#print axioms h_norm
#print axioms ell_h_orthogonal
#print axioms cross_target
#print axioms carrier_norm
#print axioms designated_sum
#print axioms a_transverse
#print axioms b_transverse
#print axioms desired_output_decomposition
#print axioms difference_output_parallel
#print axioms a_self_zero
#print axioms b_self_zero
#print axioms cross_color_radial_gap
#print axioms localization_width_sublinear

end SixColorHighHighIsolation
end NSBraid
