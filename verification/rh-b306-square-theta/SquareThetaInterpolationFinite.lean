import Mathlib

/-!
# Finite square-cell interpolation for RH B306

This file formalizes only the elementary real inequality used to pass from a
sampled lower bound at a square endpoint to every point in the following
square cell.

It does **not** formalize primes, Chebyshev functions, the prime number theorem,
Mellin transforms, Pringsheim--Landau, zeta zeros, BGST/Hankel matrices, or RH.
-/

namespace Millennium.RH.SquareThetaInterpolation

/-- Positive part on the reals. -/
def positivePart (x : ℝ) : ℝ := max x 0

/--
If the cumulative state is monotone (`thetaA <= thetaX`) and `a <= x`, then
negative depth at `x` is at most negative depth at `a` plus the physical drift
`x-a`.

This is the abstract finite inequality used with `a=n^2` in RH B306.
-/
theorem monotone_cell_positive_depth
    {a x thetaA thetaX : ℝ}
    (hax : a ≤ x)
    (htheta : thetaA ≤ thetaX) :
    positivePart (x - thetaX) ≤
      positivePart (a - thetaA) + (x - a) := by
  unfold positivePart
  have hdrift : 0 ≤ x - a := sub_nonneg.mpr hax
  have hdef : x - thetaX ≤ (a - thetaA) + (x - a) := by
    linarith
  apply max_le
  · calc
      x - thetaX ≤ (a - thetaA) + (x - a) := hdef
      _ ≤ max (a - thetaA) 0 + (x - a) := by
        exact add_le_add_right (le_max_left (a - thetaA) 0) (x - a)
  · exact add_nonneg (le_max_right (a - thetaA) 0) hdrift

/-- The width of the integer square cell `[n^2,(n+1)^2]` is `2n+1`. -/
theorem square_cell_width (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ 2 - ((n : ℝ) ^ 2)) = 2 * (n : ℝ) + 1 := by
  push_cast
  ring

/--
A convenient composed finite shell: if `x` lies between consecutive real
squares and the cumulative state is monotone, the hidden negative depth costs
at most the sampled depth plus `2n+1`.
-/
theorem square_cell_positive_depth
    (n : ℕ) {x thetaA thetaX : ℝ}
    (hlower : (n : ℝ) ^ 2 ≤ x)
    (hupper : x ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    (htheta : thetaA ≤ thetaX) :
    positivePart (x - thetaX) ≤
      positivePart ((n : ℝ) ^ 2 - thetaA) + (2 * (n : ℝ) + 1) := by
  have hbase := monotone_cell_positive_depth
    (a := (n : ℝ) ^ 2) (x := x)
    (thetaA := thetaA) (thetaX := thetaX) hlower htheta
  have hwidth : x - (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) + 1 := by
    rw [← square_cell_width n]
    linarith
  linarith

#print axioms monotone_cell_positive_depth
#print axioms square_cell_width
#print axioms square_cell_positive_depth

end Millennium.RH.SquareThetaInterpolation
