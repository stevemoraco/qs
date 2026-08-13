import Mathlib

/-!
# BSD shape/scale separation: finite-difference core

This formalizes only the elementary algebra behind the banked anticyclotomic
shape/scale theorem.  It does not formalize Selmer groups, Euler systems, or BSD.
-/

namespace BSDBraid

/-- An additive baseline disappears under one finite difference. -/
theorem baseline_cancels_in_first_difference
    {R : Type*} [AddCommGroup R]
    (D A d : ℕ → R) (c : R)
    (r : ℕ)
    (hD : ∀ n, D n = c + A n)
    (hTail : A r = d r + A (r + 1)) :
    D r - D (r + 1) = d r := by
  rw [hD r, hD (r + 1), hTail]
  abel

/-- If consecutive shell depths decrease, the baseline-shifted tail profile is
    discretely convex. -/
theorem discrete_convexity_of_decreasing_shells
    {R : Type*} [LinearOrderedRing R]
    (D A d : ℕ → R) (c : R)
    (r : ℕ)
    (hD : ∀ n, D n = c + A n)
    (hTail0 : A r = d r + A (r + 1))
    (hTail1 : A (r + 1) = d (r + 1) + A (r + 2))
    (hmono : d (r + 1) ≤ d r) :
    0 ≤ D r - 2 * D (r + 1) + D (r + 2) := by
  have h0 : D r - D (r + 1) = d r :=
    baseline_cancels_in_first_difference D A d c r hD hTail0
  have h1 : D (r + 1) - D (r + 2) = d (r + 1) :=
    baseline_cancels_in_first_difference D A d c (r + 1) hD hTail1
  linarith

/-- One scalar baseline calibration reconstructs every absolute profile value
    once its tail shape is known. -/
theorem recover_absolute_depth_from_baseline
    {R : Type*} [AddCommGroup R]
    (D A : ℕ → R) (c : R)
    (r : ℕ)
    (hD : D r = c + A r) :
    D r - c = A r := by
  rw [hD]
  abel

end BSDBraid
