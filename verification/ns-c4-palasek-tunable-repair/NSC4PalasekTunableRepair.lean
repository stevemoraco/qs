import Mathlib

namespace NSC4PalasekTunableRepair

/-- Power of the banked C4 backreaction budget after substituting
`Q = R^b` and `X = Q^(beta-alpha)`. -/
def exponent (alpha b beta : ℝ) : ℝ :=
  alpha - 1 + b * (beta - alpha) - b

/-- Exact strict parameter window used by the viscous Palasek/C4 lane. -/
def palasekWindow (alpha b beta : ℝ) : Prop :=
  2 < alpha ∧
  alpha < 5 / 2 ∧
  1 < b ∧
  b < alpha / 2 ∧
  2 * b < beta ∧
  beta < alpha

/-- A concrete positive tuning parameter small relative to both the
Palasek window width and a requested repair exponent. -/
def tunedEpsilon (alpha eta : ℝ) : ℝ :=
  min ((alpha - 2) / 6) (min (eta / 6) (1 / 6))

/-- Adjacent-shell exponent chosen close to the Palasek boundary `b = 1`. -/
def tunedB (alpha eta : ℝ) : ℝ :=
  1 + tunedEpsilon alpha eta

/-- Terminal-amplitude exponent chosen close to the boundary `beta = 2b`. -/
def tunedBeta (alpha eta : ℝ) : ℝ :=
  2 * tunedB alpha eta + tunedEpsilon alpha eta

theorem tunedEpsilon_pos
    {alpha eta : ℝ}
    (halpha : 2 < alpha)
    (heta : 0 < eta) :
    0 < tunedEpsilon alpha eta := by
  simp only [tunedEpsilon, lt_min_iff]
  constructor
  · linarith
  · constructor
    · linarith
    · norm_num

theorem tunedEpsilon_le_alpha (alpha eta : ℝ) :
    tunedEpsilon alpha eta ≤ (alpha - 2) / 6 := by
  exact min_le_left _ _

theorem tunedEpsilon_le_eta (alpha eta : ℝ) :
    tunedEpsilon alpha eta ≤ eta / 6 := by
  exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem tunedEpsilon_le_sixth (alpha eta : ℝ) :
    tunedEpsilon alpha eta ≤ 1 / 6 := by
  exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- The explicit tuning remains inside the complete strict Palasek window. -/
theorem tuned_parameter_window
    {alpha eta : ℝ}
    (halphaLow : 2 < alpha)
    (halphaHigh : alpha < 5 / 2)
    (heta : 0 < eta) :
    palasekWindow alpha (tunedB alpha eta) (tunedBeta alpha eta) := by
  have hepsPos : 0 < tunedEpsilon alpha eta :=
    tunedEpsilon_pos halphaLow heta
  have hepsAlpha : tunedEpsilon alpha eta ≤ (alpha - 2) / 6 :=
    tunedEpsilon_le_alpha alpha eta
  refine ⟨halphaLow, halphaHigh, ?_, ?_, ?_, ?_⟩
  · unfold tunedB
    linarith
  · unfold tunedB
    linarith
  · unfold tunedBeta
    linarith
  · unfold tunedBeta tunedB
    linarith

/-- Closed formula for the obstruction exponent along the tuned family. -/
theorem tuned_exponent_formula (alpha eta : ℝ) :
    exponent alpha (tunedB alpha eta) (tunedBeta alpha eta) =
      tunedEpsilon alpha eta *
        (4 + 3 * tunedEpsilon alpha eta - alpha) := by
  unfold exponent tunedB tunedBeta
  ring

/-- Positivity of the obstruction exponent for any source-admissible
strict parameter window. -/
theorem window_forces_positive_exponent
    {alpha b beta : ℝ}
    (hwindow : palasekWindow alpha b beta) :
    0 < exponent alpha b beta := by
  rcases hwindow with ⟨_, halphaHigh, hbLow, _, hbetaLow, _⟩
  have hbpos : 0 < b := by linarith
  have hfirst : 0 < b * (beta - 2 * b) :=
    mul_pos hbpos (sub_pos.mpr hbetaLow)
  have hmargin : 0 < 2 * b + 1 - alpha := by
    linarith
  have hsecond : 0 < (b - 1) * (2 * b + 1 - alpha) :=
    mul_pos (sub_pos.mpr hbLow) hmargin
  unfold exponent
  nlinarith

/-- For every strict 3D endpoint and every requested positive power `eta`,
there are source-admissible Palasek parameters whose obstruction exponent
is positive but smaller than `eta`. -/
theorem arbitrarily_small_positive_exponent
    {alpha eta : ℝ}
    (halphaLow : 2 < alpha)
    (halphaHigh : alpha < 5 / 2)
    (heta : 0 < eta) :
    let b := tunedB alpha eta
    let beta := tunedBeta alpha eta
    palasekWindow alpha b beta ∧
      0 < exponent alpha b beta ∧
      exponent alpha b beta < eta := by
  dsimp
  have hwindow :
      palasekWindow alpha (tunedB alpha eta) (tunedBeta alpha eta) :=
    tuned_parameter_window halphaLow halphaHigh heta
  have hpositive :
      0 < exponent alpha (tunedB alpha eta) (tunedBeta alpha eta) :=
    window_forces_positive_exponent hwindow
  have hepsPos : 0 < tunedEpsilon alpha eta :=
    tunedEpsilon_pos halphaLow heta
  have hepsEta : tunedEpsilon alpha eta ≤ eta / 6 :=
    tunedEpsilon_le_eta alpha eta
  have hepsSixth : tunedEpsilon alpha eta ≤ 1 / 6 :=
    tunedEpsilon_le_sixth alpha eta
  have hfactor :
      4 + 3 * tunedEpsilon alpha eta - alpha < (5 : ℝ) / 2 := by
    linarith
  have hmul1 :
      tunedEpsilon alpha eta *
          (4 + 3 * tunedEpsilon alpha eta - alpha) <
        tunedEpsilon alpha eta * ((5 : ℝ) / 2) :=
    mul_lt_mul_of_pos_left hfactor hepsPos
  have hmul2 :
      tunedEpsilon alpha eta * ((5 : ℝ) / 2) ≤
        (eta / 6) * ((5 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hepsEta (by norm_num)
  have hmul3 : (eta / 6) * ((5 : ℝ) / 2) < eta := by
    nlinarith
  have hsmall :
      exponent alpha (tunedB alpha eta) (tunedBeta alpha eta) < eta := by
    rw [tuned_exponent_formula]
    exact lt_trans hmul1 (lt_of_le_of_lt hmul2 hmul3)
  exact ⟨hwindow, hpositive, hsmall⟩

#print axioms tunedEpsilon_pos
#print axioms tunedEpsilon_le_alpha
#print axioms tunedEpsilon_le_eta
#print axioms tunedEpsilon_le_sixth
#print axioms tuned_parameter_window
#print axioms tuned_exponent_formula
#print axioms window_forces_positive_exponent
#print axioms arbitrarily_small_positive_exponent

end NSC4PalasekTunableRepair
