import Mathlib

namespace NSDLSTemporalCoefficientGate

/-- Exponent margin for the DLS temporal coefficient error when the scalar
stress is normalized by its pointwise intermittent covariance scale. -/
noncomputable def peakMargin (alpha beta b : ℝ) : ℝ :=
  b - beta + alpha - 1 - b * (alpha - beta)

/-- The exponent obtained by incorrectly feeding the spatial `L²` stress scale
into the pointwise DLS coefficient map. -/
noncomputable def l2Margin (alpha beta b : ℝ) : ℝ :=
  b - beta + (alpha - 1) / 2 - b * (alpha - beta)

/-- The pointwise-stress temporal margin factors into the scale-separation
factor and the amplitude-gap factor. -/
theorem peak_margin_factorization (alpha beta b : ℝ) :
    peakMargin alpha beta b = (b - 1) * (1 - (alpha - beta)) := by
  unfold peakMargin
  ring

/-- Throughout Palasek's viscous parameter window, the pointwise-stress DLS
temporal margin is strictly positive. -/
theorem peak_margin_positive_of_palasek_window
    {alpha beta b : ℝ}
    (hb : 1 < b)
    (hbetaLow : 2 * b < beta)
    (hbetaHigh : beta < alpha)
    (halpha : alpha ≤ 5 / 2) :
    0 < peakMargin alpha beta b := by
  have htwo : 2 < beta := by nlinarith
  have hdelta : alpha - beta < 1 := by nlinarith
  rw [peak_margin_factorization]
  exact mul_pos (sub_pos.mpr hb) (sub_pos.mpr hdelta)

/-- Exact temporal margin at the explicit `alpha = 9/4` parameter point. -/
theorem peak_margin_alpha_nine_four :
    peakMargin (9 / 4) (35 / 16) (17 / 16) = 15 / 256 := by
  norm_num [peakMargin]

/-- The same parameter point fails if the pointwise coefficient map is
mistakenly normalized by the spatial `L²` stress size. -/
theorem l2_margin_alpha_nine_four :
    l2Margin (9 / 4) (35 / 16) (17 / 16) = -(145 / 256) := by
  norm_num [l2Margin]

/-- The norm/type choice reverses the sign at the explicit parameter point. -/
theorem stress_norm_choice_reverses_sign :
    0 < peakMargin (9 / 4) (35 / 16) (17 / 16) ∧
    l2Margin (9 / 4) (35 / 16) (17 / 16) < 0 := by
  norm_num [peakMargin, l2Margin]

/-- A signed smooth amplitude realizes the same quadratic stress as its square;
this is the algebraic repair for a principal-square-root kink at activation. -/
theorem signed_amplitude_recovers_stress (h gamma : ℝ) :
    (h * gamma) ^ 2 = h ^ 2 * gamma ^ 2 := by
  ring

/-- Exact algebraic chain-rule budget after the analytic derivatives have been
bounded. This theorem contains no calculus oracle: `ht`, `dgamma`, and `qt` are
already the certified derivative values. -/
theorem coefficient_derivative_algebraic_bound
    {h ht gamma dgamma qt Lh Lq G D : ℝ}
    (hLh : 0 ≤ Lh)
    (hLq : 0 ≤ Lq)
    (hG : 0 ≤ G)
    (hD : 0 ≤ D)
    (hht : |ht| ≤ Lh)
    (hgamma : |gamma| ≤ G)
    (hdgamma : |dgamma| ≤ D)
    (hqt : |qt| ≤ Lq) :
    |ht * gamma + h * dgamma * qt| ≤ Lh * G + |h| * D * Lq := by
  have htri :
      |ht * gamma + h * dgamma * qt| ≤
        |ht * gamma| + |h * dgamma * qt| := by
    apply (abs_le).2
    constructor
    · have hx := (abs_le).1 (le_refl |ht * gamma|)
      have hy := (abs_le).1 (le_refl |h * dgamma * qt|)
      linarith [hx.1, hy.1]
    · have hx := (abs_le).1 (le_refl |ht * gamma|)
      have hy := (abs_le).1 (le_refl |h * dgamma * qt|)
      linarith [hx.2, hy.2]
  calc
    |ht * gamma + h * dgamma * qt| ≤
        |ht * gamma| + |h * dgamma * qt| := htri
    _ = |ht| * |gamma| + |h| * |dgamma| * |qt| := by
      simp [abs_mul, mul_assoc]
    _ ≤ Lh * G + |h| * D * Lq := by
      have hfirst : |ht| * |gamma| ≤ Lh * G :=
        mul_le_mul hht hgamma (abs_nonneg gamma) hLh
      have hsecondA : |h| * |dgamma| ≤ |h| * D :=
        mul_le_mul_of_nonneg_left hdgamma (abs_nonneg h)
      have hsecondB : |h| * |dgamma| * |qt| ≤ |h| * D * |qt| :=
        mul_le_mul_of_nonneg_right hsecondA (abs_nonneg qt)
      have hsecondC : |h| * D * |qt| ≤ |h| * D * Lq :=
        mul_le_mul_of_nonneg_left hqt (mul_nonneg (abs_nonneg h) hD)
      exact add_le_add hfirst (hsecondB.trans hsecondC)

/-- The scalar temporal gate: a lower bound on `K * tau * h` transfers directly
to an upper bound on the relative anti-divergence defect. -/
theorem relative_temporal_defect_bound
    {K tau h eps : ℝ}
    (hK : 0 < K)
    (htau : 0 < tau)
    (hh : 0 < h)
    (hgate : 1 ≤ eps * (K * tau * h)) :
    1 / (K * tau * h) ≤ eps := by
  have hden : 0 < K * tau * h := mul_pos (mul_pos hK htau) hh
  exact (div_le_iff₀ hden).2 (by simpa [mul_assoc] using hgate)

/-- A purely relative one-step bound cannot activate a mode from exact zero. -/
theorem zero_start_relative_bound_cannot_activate
    {h0 h1 C : ℝ}
    (hzero : h0 = 0)
    (hnonneg : 0 ≤ h1)
    (hrelative : h1 ≤ C * h0) :
    h1 = 0 := by
  subst h0
  norm_num at hrelative
  exact le_antisymm hrelative hnonneg

#print axioms peak_margin_factorization
#print axioms peak_margin_positive_of_palasek_window
#print axioms peak_margin_alpha_nine_four
#print axioms l2_margin_alpha_nine_four
#print axioms stress_norm_choice_reverses_sign
#print axioms signed_amplitude_recovers_stress
#print axioms coefficient_derivative_algebraic_bound
#print axioms relative_temporal_defect_bound
#print axioms zero_start_relative_bound_cannot_activate

end NSDLSTemporalCoefficientGate
