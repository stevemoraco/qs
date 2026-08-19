import Mathlib

/-!
# RH Run10bzEC — exact Bezout two-lift parameterization

Finite integer-algebra core only.  Given the two reduced band equations and an
explicit Bezout certificate, the four integer variables lie on two affine
integer lines and the 2x2 determinant is exactly the Poisson frequency times
the sum of the two lift indices.

This file does not formalize Heath--Brown identities, dispersion estimates,
Suzuki's criterion, zeta, or RH.
-/

namespace Millennium.RH.Run10bzecBezoutTwoLiftParameterization

/-- Every solution of the two reduced band equations has an exact two-lift
Bezout parameterization, and the determinant slope is the sum of those lifts. -/
theorem bezout_two_lift_parameterization
    (A B l₁ l₂ a b h x y : ℤ)
    (h₁ : A * b - l₁ * a = h)
    (h₂ : B * a - l₂ * b = h)
    (hbez : x * a + y * b = 1) :
    ∃ t u : ℤ,
      t = x * A + y * l₁ ∧
      u = y * B + x * l₂ ∧
      A = h * y + a * t ∧
      l₁ = b * t - h * x ∧
      B = h * x + b * u ∧
      l₂ = a * u - h * y ∧
      A * B - l₁ * l₂ = h * (t + u) := by
  let t : ℤ := x * A + y * l₁
  let u : ℤ := y * B + x * l₂
  have hA : A = h * y + a * t := by
    calc
      A = A * (x * a + y * b) := by rw [hbez]; ring
      _ = (A * b - l₁ * a) * y + a * (x * A + y * l₁) := by ring
      _ = h * y + a * t := by rw [h₁]
  have hl₁ : l₁ = b * t - h * x := by
    calc
      l₁ = l₁ * (x * a + y * b) := by rw [hbez]; ring
      _ = b * (x * A + y * l₁) - (A * b - l₁ * a) * x := by ring
      _ = b * t - h * x := by rw [h₁]
  have hB : B = h * x + b * u := by
    calc
      B = B * (x * a + y * b) := by rw [hbez]; ring
      _ = (B * a - l₂ * b) * x + b * (y * B + x * l₂) := by ring
      _ = h * x + b * u := by rw [h₂]
  have hl₂ : l₂ = a * u - h * y := by
    calc
      l₂ = l₂ * (x * a + y * b) := by rw [hbez]; ring
      _ = a * (y * B + x * l₂) - (B * a - l₂ * b) * y := by ring
      _ = a * u - h * y := by rw [h₂]
  have hD : A * B - l₁ * l₂ = h * (t + u) := by
    calc
      A * B - l₁ * l₂ =
          (h * y + a * t) * (h * x + b * u) -
            (b * t - h * x) * (a * u - h * y) := by
              rw [hA, hl₁, hB, hl₂]
      _ = h * (t + u) * (x * a + y * b) := by ring
      _ = h * (t + u) := by rw [hbez]; ring
  exact ⟨t, u, rfl, rfl, hA, hl₁, hB, hl₂, hD⟩

/-- Converse: arbitrary lift indices give a solution of the two band equations. -/
theorem two_lift_formulas_satisfy_system
    (a b h x y t u : ℤ)
    (hbez : x * a + y * b = 1) :
    let A : ℤ := h * y + a * t
    let l₁ : ℤ := b * t - h * x
    let B : ℤ := h * x + b * u
    let l₂ : ℤ := a * u - h * y
    A * b - l₁ * a = h ∧
      B * a - l₂ * b = h ∧
      A * B - l₁ * l₂ = h * (t + u) := by
  dsimp
  constructor
  · calc
      (h * y + a * t) * b - (b * t - h * x) * a =
          h * (x * a + y * b) := by ring
      _ = h := by rw [hbez]; ring
  constructor
  · calc
      (h * x + b * u) * a - (a * u - h * y) * b =
          h * (x * a + y * b) := by ring
      _ = h := by rw [hbez]; ring
  · calc
      (h * y + a * t) * (h * x + b * u) -
          (b * t - h * x) * (a * u - h * y) =
            h * (t + u) * (x * a + y * b) := by ring
      _ = h * (t + u) := by rw [hbez]; ring

/-- The lift indices are exactly recovered from the affine formulas. -/
theorem recover_lift_indices
    (A B l₁ l₂ a b h x y t u : ℤ)
    (hbez : x * a + y * b = 1)
    (hA : A = h * y + a * t)
    (hl₁ : l₁ = b * t - h * x)
    (hB : B = h * x + b * u)
    (hl₂ : l₂ = a * u - h * y) :
    x * A + y * l₁ = t ∧ y * B + x * l₂ = u := by
  constructor
  · calc
      x * A + y * l₁ =
          x * (h * y + a * t) + y * (b * t - h * x) := by rw [hA, hl₁]
      _ = t * (x * a + y * b) := by ring
      _ = t := by rw [hbez]; ring
  · calc
      y * B + x * l₂ =
          y * (h * x + b * u) + x * (a * u - h * y) := by rw [hB, hl₂]
      _ = u * (x * a + y * b) := by ring
      _ = u := by rw [hbez]; ring

/-- At nonzero Poisson frequency, determinant zero is exactly cancellation of
the two lift indices. -/
theorem zero_determinant_iff_lifts_cancel
    (A B l₁ l₂ h t u : ℤ)
    (hh : h ≠ 0)
    (hD : A * B - l₁ * l₂ = h * (t + u)) :
    A * B - l₁ * l₂ = 0 ↔ t + u = 0 := by
  constructor
  · intro hz
    have hzero : h * (t + u) = 0 := by rw [← hD, hz]
    exact (mul_eq_zero.mp hzero).resolve_left hh
  · intro htu
    rw [hD, htu]
    ring

#print axioms bezout_two_lift_parameterization
#print axioms two_lift_formulas_satisfy_system
#print axioms recover_lift_indices
#print axioms zero_determinant_iff_lifts_cancel

end Millennium.RH.Run10bzecBezoutTwoLiftParameterization
