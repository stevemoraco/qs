import Mathlib

namespace RHCausalSmoothedReserveFinite

/-- Algebraic form of the causal-smoothed ordinary-prime reserve on one prime gap.
Here `s` stands for `sqrt x`, while `A` and `B` are the frozen weighted prime moments. -/
def gapH (x s A B : ℝ) : ℝ :=
  (4 / 3 : ℝ) * (s - 1 / x) - A + B / x

/-- Numerator governing the sign of the gap derivative after multiplying by `x^2`.
When `s = sqrt x`, this is `(2/3) x^(3/2) + 4/3 - B`. -/
def slopeNumerator (x s B : ℝ) : ℝ :=
  (2 / 3 : ℝ) * x * s + 4 / 3 - B

/-- Adding one prime atom of weighted size `a` changes `A` by `a` and `B` by
`x*a`. These jumps cancel exactly in the smoothed reserve at the arrival point. -/
theorem prime_jump_continuity
    {x s A B a : ℝ}
    (hx : x ≠ 0) :
    gapH x s (A + a) (B + x * a) = gapH x s A B := by
  unfold gapH
  field_simp [hx]
  ring

/-- Vanishing of the formal gap-slope numerator is exactly the cubic-moment
balance used to locate the sole possible interior critical point. -/
theorem slope_zero_iff
    {x s B : ℝ} :
    slopeNumerator x s B = 0 ↔
      B = (2 / 3 : ℝ) * x * s + 4 / 3 := by
  unfold slopeNumerator
  constructor <;> intro h <;> linarith

/-- At a critical point, the complicated two-moment reserve collapses exactly
to `2*s-A`. -/
theorem critical_value
    {x s A B : ℝ}
    (hx : x ≠ 0)
    (hB : B = (2 / 3 : ℝ) * x * s + 4 / 3) :
    gapH x s A B = 2 * s - A := by
  rw [hB]
  unfold gapH
  field_simp [hx]
  ring

/-- Therefore positivity at an interior critical point is exactly the first-
moment inequality `A <= 2*s`. -/
theorem critical_nonnegative_iff
    {x s A B : ℝ}
    (hx : x ≠ 0)
    (hB : B = (2 / 3 : ℝ) * x * s + 4 / 3) :
    0 ≤ gapH x s A B ↔ A ≤ 2 * s := by
  rw [critical_value hx hB]
  linarith

/-- If additionally `x=s^2`, the critical balance is equivalent to the cubic
moment identity `12*B-16 = 8*s^3`. This is the algebraic spine behind a purely
finite gap-minimum certificate. -/
theorem critical_cubic_moment
    {x s B : ℝ}
    (hx : x = s ^ 2)
    (hB : B = (2 / 3 : ℝ) * x * s + 4 / 3) :
    12 * B - 16 = 8 * s ^ 3 := by
  rw [hB, hx]
  ring

/-- For nonnegative `A,s`, the critical first-moment inequality is equivalent
to a cubic inequality. -/
theorem critical_first_moment_cubic_iff
    {A s : ℝ}
    (hA : 0 ≤ A)
    (hs : 0 ≤ s) :
    A ≤ 2 * s ↔ A ^ 3 ≤ 8 * s ^ 3 := by
  constructor
  · intro h
    nlinarith [sq_nonneg A, sq_nonneg s,
      mul_nonneg hA (sq_nonneg A), mul_nonneg hs (sq_nonneg s)]
  · intro h
    by_contra hnot
    have hgt : 2 * s < A := lt_of_not_ge hnot
    nlinarith [sq_nonneg A, sq_nonneg s,
      mul_nonneg hA (sq_nonneg A), mul_nonneg hs (sq_nonneg s)]

#print axioms prime_jump_continuity
#print axioms slope_zero_iff
#print axioms critical_value
#print axioms critical_nonnegative_iff
#print axioms critical_cubic_moment
#print axioms critical_first_moment_cubic_iff

end RHCausalSmoothedReserveFinite
