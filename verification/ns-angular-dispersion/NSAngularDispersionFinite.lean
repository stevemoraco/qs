import Mathlib

/-!
# Navier–Stokes angular-dispersion finite algebra core

HONESTY BOUNDARY

This file formalizes only elementary three-coordinate identities used by the
human compactness theorem:

* Lagrange's identity for the squared cross product;
* exact reconstruction of a vector from its scalar projection onto a unit axis
  when its cross product with that axis vanishes.

It does not formalize measurable vector fields, Lorentz spaces, weak
convergence, divergence-free distributions, compactness, blowup limits, the
Navier–Stokes equations, or the Clay problem.
-/

namespace MillenniumBraid
namespace NSAngularDispersionFinite

/-- Three-coordinate Lagrange identity:
`|v × e|² = |v|² |e|² - (v · e)²`. -/
theorem cross_sq_lagrange
    (x y z a b c : ℝ) :
    (y * c - z * b) ^ 2 +
        (z * a - x * c) ^ 2 +
        (x * b - y * a) ^ 2 =
      (x ^ 2 + y ^ 2 + z ^ 2) *
          (a ^ 2 + b ^ 2 + c ^ 2) -
        (x * a + y * b + z * c) ^ 2 := by
  ring

/-- If `e=(a,b,c)` is a unit vector and `v × e=0`, then
`v=(v·e)e` coordinate by coordinate. -/
theorem reconstruct_from_zero_cross
    (x y z a b c : ℝ)
    (hunit : a ^ 2 + b ^ 2 + c ^ 2 = 1)
    (hcross₁ : y * c - z * b = 0)
    (hcross₂ : z * a - x * c = 0)
    (hcross₃ : x * b - y * a = 0) :
    let d := x * a + y * b + z * c
    x = d * a ∧ y = d * b ∧ z = d * c := by
  let d := x * a + y * b + z * c
  have hxc : x * c - z * a = 0 := by linarith
  have hya : y * a - x * b = 0 := by linarith
  have hzb : z * b - y * c = 0 := by linarith
  have hx : x = d * a := by
    calc
      x = x * (a ^ 2 + b ^ 2 + c ^ 2) := by rw [hunit]; ring
      _ = d * a + b * (x * b - y * a) +
            c * (x * c - z * a) := by
        dsimp [d]
        ring
      _ = d * a := by rw [hcross₃, hxc]; ring
  have hy : y = d * b := by
    calc
      y = y * (a ^ 2 + b ^ 2 + c ^ 2) := by rw [hunit]; ring
      _ = d * b + a * (y * a - x * b) +
            c * (y * c - z * b) := by
        dsimp [d]
        ring
      _ = d * b := by rw [hya, hcross₁]; ring
  have hz : z = d * c := by
    calc
      z = z * (a ^ 2 + b ^ 2 + c ^ 2) := by rw [hunit]; ring
      _ = d * c + a * (z * a - x * c) +
            b * (z * b - y * c) := by
        dsimp [d]
        ring
      _ = d * c := by rw [hcross₂, hzb]; ring
  exact ⟨hx, hy, hz⟩

/-- Zero squared angular dispersion is exactly zero cross product, since it is
a sum of three real squares. -/
theorem zero_cross_of_zero_cross_sq
    (x y z a b c : ℝ)
    (hzero :
      (y * c - z * b) ^ 2 +
          (z * a - x * c) ^ 2 +
          (x * b - y * a) ^ 2 = 0) :
    y * c - z * b = 0 ∧
      z * a - x * c = 0 ∧
      x * b - y * a = 0 := by
  have h₁ : 0 ≤ (y * c - z * b) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ (z * a - x * c) ^ 2 := sq_nonneg _
  have h₃ : 0 ≤ (x * b - y * a) ^ 2 := sq_nonneg _
  have hz₁ : (y * c - z * b) ^ 2 = 0 := by nlinarith
  have hz₂ : (z * a - x * c) ^ 2 = 0 := by nlinarith
  have hz₃ : (x * b - y * a) ^ 2 = 0 := by nlinarith
  exact ⟨sq_eq_zero_iff.mp hz₁, sq_eq_zero_iff.mp hz₂,
    sq_eq_zero_iff.mp hz₃⟩

#print axioms cross_sq_lagrange
#print axioms reconstruct_from_zero_cross
#print axioms zero_cross_of_zero_cross_sq

end NSAngularDispersionFinite
end MillenniumBraid
