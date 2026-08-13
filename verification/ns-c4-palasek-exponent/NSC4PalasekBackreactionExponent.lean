import Mathlib

namespace NSC4PalasekBackreactionExponent

/-- Power of the banked C4 backreaction budget after substituting
`Q = R^b` and `X = Q^(beta-alpha)`. -/
def exponent (alpha b beta : ℝ) : ℝ :=
  alpha - 1 + b * (beta - alpha) - b

/-- Exact decomposition into two terms which are positive in the Palasek window. -/
theorem exponent_decomposition (alpha b beta : ℝ) :
    exponent alpha b beta =
      b * (beta - 2 * b) + (b - 1) * (2 * b + 1 - alpha) := by
  unfold exponent
  ring

/-- The strict C4 three-dimensional endpoint gives a positive angular margin. -/
theorem angular_margin_pos
    {alpha b : ℝ}
    (hb : 1 < b)
    (halpha : alpha < 5 / 2) :
    0 < 2 * b + 1 - alpha := by
  linarith

/-- Minimal source hypotheses already force the C4 budget exponent to be positive. -/
theorem exponent_pos_minimal
    {alpha b beta : ℝ}
    (hb : 1 < b)
    (halpha : alpha < 5 / 2)
    (hbeta : 2 * b < beta) :
    0 < exponent alpha b beta := by
  have hbpos : 0 < b := by linarith
  have hfirst : 0 < b * (beta - 2 * b) :=
    mul_pos hbpos (sub_pos.mpr hbeta)
  have hmargin : 0 < 2 * b + 1 - alpha :=
    angular_margin_pos hb halpha
  have hsecond : 0 < (b - 1) * (2 * b + 1 - alpha) :=
    mul_pos (sub_pos.mpr hb) hmargin
  rw [exponent_decomposition]
  exact add_pos hfirst hsecond

/-- Exact Palasek viscous/C4 parameter window implies positive budget exponent. -/
theorem palasek_window_forces_positive_exponent
    {alpha b beta : ℝ}
    (halphaLow : 2 < alpha)
    (halphaHigh : alpha < 5 / 2)
    (hbLow : 1 < b)
    (hbHigh : b < alpha / 2)
    (hbetaLow : 2 * b < beta)
    (hbetaHigh : beta < alpha) :
    0 < exponent alpha b beta := by
  exact exponent_pos_minimal hbLow halphaHigh hbetaLow

/-- The reciprocal separation ratio has the opposite, strictly negative exponent. -/
theorem required_separation_exponent_negative
    {alpha b beta : ℝ}
    (hb : 1 < b)
    (halpha : alpha < 5 / 2)
    (hbeta : 2 * b < beta) :
    b - (alpha - 1) - b * (beta - alpha) < 0 := by
  have hpos := exponent_pos_minimal hb halpha hbeta
  unfold exponent at hpos
  linarith

/-- A transparent rational point in the full Palasek parameter window. -/
theorem sample_parameter_window :
    (2 : ℝ) < 9 / 4 ∧
    (1 : ℝ) < 11 / 10 ∧
    (11 : ℝ) / 10 < ((9 : ℝ) / 4) / 2 ∧
    2 * ((11 : ℝ) / 10) < (89 : ℝ) / 40 ∧
    (89 : ℝ) / 40 < (9 : ℝ) / 4 := by
  norm_num

/-- The sample point has exact positive exponent `49/400`. -/
theorem sample_exponent :
    exponent ((9 : ℝ) / 4) ((11 : ℝ) / 10) ((89 : ℝ) / 40) =
      (49 : ℝ) / 400 := by
  norm_num [exponent]

#print axioms exponent_decomposition
#print axioms angular_margin_pos
#print axioms exponent_pos_minimal
#print axioms palasek_window_forces_positive_exponent
#print axioms required_separation_exponent_negative
#print axioms sample_parameter_window
#print axioms sample_exponent

end NSC4PalasekBackreactionExponent
