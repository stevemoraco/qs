import Mathlib

namespace RHTriangularSpline

/-- Middle branch of `a^3 C(ell/a)` for `ell/2 <= a <= ell`. -/
def qMid (a ell : ℝ) : ℝ := (2 * a - ell) ^ 3 / 6

/-- High branch of `a^3 C(ell/a)` for `a >= ell`. -/
def qHigh (a ell : ℝ) : ℝ := (2 / 3 : ℝ) * a ^ 3 - ell ^ 2 * a + ell ^ 3 / 2

/-- Formal first derivatives of the two polynomial branches. -/
def qMidD1 (a ell : ℝ) : ℝ := (2 * a - ell) ^ 2
def qHighD1 (a ell : ℝ) : ℝ := 2 * a ^ 2 - ell ^ 2

/-- Formal second derivatives of the two polynomial branches. -/
def qMidD2 (a ell : ℝ) : ℝ := 4 * (2 * a - ell)
def qHighD2 (a ell : ℝ) : ℝ := 4 * a

/-- Formal third derivatives of the polynomial branches. -/
def qMidD3 : ℝ := 8
def qHighD3 : ℝ := 4

/-- At the activation knot `a=ell/2`, the middle cubic has zero value. -/
theorem activation_value (ell : ℝ) : qMid (ell / 2) ell = 0 := by
  simp [qMid]
  ring

/-- At the activation knot, the first derivative also vanishes. -/
theorem activation_d1 (ell : ℝ) : qMidD1 (ell / 2) ell = 0 := by
  simp [qMidD1]
  ring

/-- At the activation knot, the second derivative also vanishes. -/
theorem activation_d2 (ell : ℝ) : qMidD2 (ell / 2) ell = 0 := by
  simp [qMidD2]
  ring

/-- The middle and high cubic branches agree at the second knot `a=ell`. -/
theorem join_value (ell : ℝ) : qMid ell ell = qHigh ell ell := by
  simp [qMid, qHigh]
  ring

/-- Their first formal derivatives agree at `a=ell`. -/
theorem join_d1 (ell : ℝ) : qMidD1 ell ell = qHighD1 ell ell := by
  simp [qMidD1, qHighD1]
  ring

/-- Their second formal derivatives agree at `a=ell`. -/
theorem join_d2 (ell : ℝ) : qMidD2 ell ell = qHighD2 ell ell := by
  simp [qMidD2, qHighD2]
  ring

/-- The third-derivative jump at the activation knot is `+8`. -/
theorem activation_third_jump : qMidD3 - 0 = 8 := by
  norm_num [qMidD3]

/-- The third-derivative jump at the second knot is `-4`. -/
theorem join_third_jump : qHighD3 - qMidD3 = -4 := by
  norm_num [qHighD3, qMidD3]

/-- Algebraic sign firewall for an even prime-power renewal knot.
If `y = p^{-m/2}` lies strictly between `0` and `1/2`, then the normalized
same-prime coefficient `4 L y (2y-1)` is strictly negative for `L>0`. -/
theorem even_knot_negative
    {L y : ℝ}
    (hL : 0 < L)
    (hy0 : 0 < y)
    (hyhalf : y < 1 / 2) :
    4 * L * y * (2 * y - 1) < 0 := by
  have hfactor : 2 * y - 1 < 0 := by linarith
  have hpos : 0 < 4 * L * y := by positivity
  exact mul_neg_of_pos_of_neg hpos hfactor

/-- Consequently no theorem may treat every raw dyadic-renewal impulse as
nonnegative merely from positivity of the von Mangoldt weights. -/
theorem raw_positive_impulse_cone_counterexample :
    4 * (1 : ℝ) * (1 / 5 : ℝ) * (2 * (1 / 5 : ℝ) - 1) < 0 := by
  norm_num

#print axioms activation_value
#print axioms activation_d1
#print axioms activation_d2
#print axioms join_value
#print axioms join_d1
#print axioms join_d2
#print axioms activation_third_jump
#print axioms join_third_jump
#print axioms even_knot_negative
#print axioms raw_positive_impulse_cone_counterexample

end RHTriangularSpline
