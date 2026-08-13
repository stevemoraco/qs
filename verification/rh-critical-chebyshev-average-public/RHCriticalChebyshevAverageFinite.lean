import Mathlib

namespace RHCriticalChebyshevAverageFinite

/-- Finite prime-gap margin for the critical weighted Chebyshev-average RH criterion.
`s` represents `sqrt x`, `theta` the frozen Chebyshev prefix, `A` the frozen
first weighted prime moment, and `c` the fixed boundary constant `sqrt 2`. -/
noncomputable def margin (s theta A c : ℝ) : ℝ :=
  s + theta / s - c - A

/-- At a prime arrival, `theta` jumps by `ell=log q` and the first weighted
moment jumps by `ell/s`. These two jumps cancel exactly. -/
theorem prime_jump_continuity
    {s theta A c ell : ℝ}
    (hs : s ≠ 0) :
    margin s (theta + ell) (A + ell / s) c = margin s theta A c := by
  unfold margin
  field_simp [hs]
  ring

/-- The formal derivative numerator on a prime gap is `x-theta`; hence any
interior critical point must satisfy `x=theta`. -/
theorem slope_zero_iff {x theta : ℝ} :
    x - theta = 0 ↔ x = theta := by
  constructor <;> intro h <;> linarith

/-- At a critical point, if `theta=s^2`, the margin collapses to
`2*s-c-A`. -/
theorem critical_value
    {s theta A c : ℝ}
    (hs : s ≠ 0)
    (htheta : theta = s ^ 2) :
    margin s theta A c = 2 * s - c - A := by
  rw [htheta]
  unfold margin
  field_simp [hs]
  ring

/-- Therefore strict positivity at a critical point is exactly
`A+c < 2*s`. -/
theorem critical_positive_iff
    {s theta A c : ℝ}
    (hs : s ≠ 0)
    (htheta : theta = s ^ 2) :
    0 < margin s theta A c ↔ A + c < 2 * s := by
  rw [critical_value hs htheta]
  constructor <;> intro h <;> linarith

/-- Squaring preserves the critical inequality when both sides are
nonnegative. This is the algebraic finite certificate used in Round237. -/
theorem critical_square_iff
    {s A c : ℝ}
    (hs : 0 ≤ s)
    (hAc : 0 ≤ A + c) :
    A + c < 2 * s ↔ (A + c) ^ 2 < 4 * s ^ 2 := by
  constructor
  · intro h
    have hsum : 0 < (2 * s - (A + c)) := by linarith
    have hplus : 0 < 2 * s + (A + c) := by linarith
    have hprod : 0 < (2 * s - (A + c)) * (2 * s + (A + c)) :=
      mul_pos hsum hplus
    nlinarith [hprod]
  · intro h
    by_contra hnot
    have hge : 2 * s ≤ A + c := le_of_not_gt hnot
    have hdiff : 0 ≤ (A + c) - 2 * s := by linarith
    have hplus : 0 ≤ (A + c) + 2 * s := by linarith
    have hprod : 0 ≤ ((A + c) - 2 * s) * ((A + c) + 2 * s) :=
      mul_nonneg hdiff hplus
    nlinarith [hprod]

/-- Combining `theta=s^2` with the squared certificate gives the exact
prime-prefix form `(A+c)^2 < 4*theta`. -/
theorem critical_prefix_square_iff
    {s theta A c : ℝ}
    (hs : 0 ≤ s)
    (htheta : theta = s ^ 2)
    (hAc : 0 ≤ A + c) :
    A + c < 2 * s ↔ (A + c) ^ 2 < 4 * theta := by
  rw [htheta]
  exact critical_square_iff hs hAc

#print axioms prime_jump_continuity
#print axioms slope_zero_iff
#print axioms critical_value
#print axioms critical_positive_iff
#print axioms critical_square_iff
#print axioms critical_prefix_square_iff

end RHCriticalChebyshevAverageFinite
