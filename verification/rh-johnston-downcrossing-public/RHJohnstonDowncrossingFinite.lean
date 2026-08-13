import Mathlib

namespace RHJohnstonDowncrossingFinite

/-- On a prime gap, after writing `x=s^2`, the source-backed weighted RH margin
has the finite algebraic form `s + theta/s - c - A`.  This file formalizes only
that finite gap algebra; it does not define primes, Chebyshev theta, zeta, or RH. -/
noncomputable def gapMargin (s theta A c : ℝ) : ℝ :=
  s + theta / s - c - A

/-- At a prime arrival, adding an atom to `theta` and the correspondingly scaled
atom to `A` leaves the margin continuous. -/
theorem arrival_continuity
    {s theta A c atom : ℝ}
    (hs : s ≠ 0) :
    gapMargin s (theta + atom) (A + atom / s) c =
      gapMargin s theta A c := by
  unfold gapMargin
  field_simp [hs]
  ring

/-- Exact calculus-free increment law on a frozen gap. -/
theorem gap_increment_factorization
    {s t theta A c : ℝ}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    gapMargin t theta A c - gapMargin s theta A c =
      (t - s) * (s * t - theta) / (s * t) := by
  unfold gapMargin
  field_simp [hs, ht]
  ring

/-- If `s <= t` and the frozen Chebyshev mass lies below `s*t`, the margin is
nondecreasing between the two square-root coordinates. -/
theorem gap_nondecreasing
    {s t theta A c : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (hst : s ≤ t) (hbelow : theta ≤ s * t) :
    gapMargin s theta A c ≤ gapMargin t theta A c := by
  have hden : 0 < s * t := mul_pos hs ht
  have h1 : 0 ≤ t - s := by linarith
  have h2 : 0 ≤ s * t - theta := by linarith
  have hp : 0 ≤ (t - s) * (s * t - theta) := mul_nonneg h1 h2
  have hq : 0 ≤ (t - s) * (s * t - theta) / (s * t) :=
    div_nonneg hp (le_of_lt hden)
  have hf := gap_increment_factorization (theta := theta) (A := A) (c := c)
    (ne_of_gt hs) (ne_of_gt ht)
  linarith

/-- If `s <= t` and the frozen Chebyshev mass lies above `s*t`, the margin is
nonincreasing between the two square-root coordinates. -/
theorem gap_nonincreasing
    {s t theta A c : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (hst : s ≤ t) (habove : s * t ≤ theta) :
    gapMargin t theta A c ≤ gapMargin s theta A c := by
  have hden : 0 < s * t := mul_pos hs ht
  have h1 : 0 ≤ t - s := by linarith
  have h2 : s * t - theta ≤ 0 := by linarith
  have hp : (t - s) * (s * t - theta) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1 h2
  have hq : (t - s) * (s * t - theta) / (s * t) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hp (le_of_lt hden)
  have hf := gap_increment_factorization (theta := theta) (A := A) (c := c)
    (ne_of_gt hs) (ne_of_gt ht)
  linarith

/-- If the frozen Chebyshev coordinate is `theta=s^2`, then `s` is the exact
finite critical coordinate and the margin collapses to `2*s-c-A`. -/
theorem critical_value
    {s theta A c : ℝ}
    (hs : s ≠ 0) (htheta : theta = s ^ 2) :
    gapMargin s theta A c = 2 * s - c - A := by
  rw [htheta]
  unfold gapMargin
  field_simp [hs]
  ring

/-- Exact excess above the critical value.  It is a square divided by the
comparison coordinate, so no derivative argument is required. -/
theorem critical_excess_identity
    {s u theta A c : ℝ}
    (hu : u ≠ 0) (htheta : theta = s ^ 2) :
    gapMargin u theta A c - (2 * s - c - A) =
      (u - s) ^ 2 / u := by
  rw [htheta]
  unfold gapMargin
  field_simp [hu]
  ring

/-- For positive square-root coordinates, the critical coordinate is a global
minimum of the frozen-gap algebraic profile. -/
theorem critical_is_minimum
    {s u theta A c : ℝ}
    (hs : 0 < s) (hu : 0 < u) (htheta : theta = s ^ 2) :
    gapMargin s theta A c ≤ gapMargin u theta A c := by
  have hid := critical_excess_identity (A := A) (c := c)
    (ne_of_gt hu) htheta
  have hsq : 0 ≤ (u - s) ^ 2 := sq_nonneg (u - s)
  have hdiv : 0 ≤ (u - s) ^ 2 / u :=
    div_nonneg hsq (le_of_lt hu)
  have hcrit := critical_value (A := A) (c := c) (ne_of_gt hs) htheta
  linarith

/-- The dangerous-gap first-moment test can be squared without loss when all
quantities have the natural nonnegative signs. -/
theorem dangerous_gap_square_iff
    {s theta A c : ℝ}
    (hs : 0 < s) (htheta : theta = s ^ 2)
    (hAc : 0 ≤ A + c) :
    A + c < 2 * s ↔ (A + c) ^ 2 < 4 * theta := by
  rw [htheta]
  constructor
  · intro h
    nlinarith [sq_nonneg (A + c - 2 * s)]
  · intro h
    by_contra hnot
    have hge : 2 * s ≤ A + c := le_of_not_gt hnot
    nlinarith [sq_nonneg (A + c - 2 * s)]

#print axioms arrival_continuity
#print axioms gap_increment_factorization
#print axioms gap_nondecreasing
#print axioms gap_nonincreasing
#print axioms critical_value
#print axioms critical_excess_identity
#print axioms critical_is_minimum
#print axioms dangerous_gap_square_iff

end RHJohnstonDowncrossingFinite
