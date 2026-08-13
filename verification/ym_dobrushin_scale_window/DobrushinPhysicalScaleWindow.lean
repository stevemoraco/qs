import Mathlib

namespace Millennium.YangMills.DobrushinPhysicalScaleWindow

noncomputable def contractionFromExponent (gamma : ℝ) : ℝ :=
  Real.exp (-gamma)

noncomputable def normalizedRate (q s : ℝ) : ℝ :=
  -Real.log q / s

theorem neg_log_contraction (gamma : ℝ) :
    -Real.log (contractionFromExponent gamma) = gamma := by
  simp [contractionFromExponent]

theorem normalizedRate_contraction (gamma s : ℝ) :
    normalizedRate (contractionFromExponent gamma) s = gamma / s := by
  simp [normalizedRate, contractionFromExponent]

theorem normalized_rate_window
    {gamma s lower upper : ℝ}
    (hs : 0 < s)
    (hlower : lower * s ≤ gamma)
    (hupper : gamma ≤ upper * s) :
    lower ≤ gamma / s ∧ gamma / s ≤ upper := by
  constructor
  · exact (le_div_iff₀ hs).2 hlower
  · exact (div_le_iff₀ hs).2 hupper

theorem contraction_window_of_exponent_window
    {gamma s lower upper : ℝ}
    (hlower : lower * s ≤ gamma)
    (hupper : gamma ≤ upper * s) :
    Real.exp (-(upper * s)) ≤ contractionFromExponent gamma ∧
      contractionFromExponent gamma ≤ Real.exp (-(lower * s)) := by
  constructor
  · unfold contractionFromExponent
    exact Real.exp_le_exp.mpr (neg_le_neg hupper)
  · unfold contractionFromExponent
    exact Real.exp_le_exp.mpr (neg_le_neg hlower)

theorem block_physical_ratio_identity
    {gamma a ell Lambda : ℝ}
    (ha : a ≠ 0) (hell : ell ≠ 0) (hLambda : Lambda ≠ 0) :
    (gamma / (a * ell)) / Lambda = gamma / (a * ell * Lambda) := by
  field_simp [ha, hell, hLambda]

theorem block_decay_window_is_physical_window
    {gamma a ell Lambda lower upper : ℝ}
    (ha : 0 < a) (hell : 0 < ell) (hLambda : 0 < Lambda)
    (hlower : lower * (a * ell * Lambda) ≤ gamma)
    (hupper : gamma ≤ upper * (a * ell * Lambda)) :
    lower ≤ (gamma / (a * ell)) / Lambda ∧
      (gamma / (a * ell)) / Lambda ≤ upper := by
  have hs : 0 < a * ell * Lambda := by positivity
  have hwindow := normalized_rate_window hs hlower hupper
  have hid : (gamma / (a * ell)) / Lambda = gamma / (a * ell * Lambda) :=
    block_physical_ratio_identity (ne_of_gt ha) (ne_of_gt hell) (ne_of_gt hLambda)
  rw [hid]
  exact hwindow

theorem fixed_exponent_overshoots_any_ratio
    {gamma R : ℝ}
    (hgamma : 0 < gamma)
    (hR : 0 ≤ R) :
    ∃ s : ℝ, 0 < s ∧ R < gamma / s := by
  let s : ℝ := gamma / (R + 1)
  have hRp : 0 < R + 1 := by linarith
  have hs : 0 < s := by
    dsimp [s]
    positivity
  refine ⟨s, hs, ?_⟩
  have hcalc : gamma / s = R + 1 := by
    dsimp [s]
    field_simp [ne_of_gt hgamma, ne_of_gt hRp]
  rw [hcalc]
  linarith

theorem fixed_contraction_overshoots_any_ratio
    {gamma R : ℝ}
    (hgamma : 0 < gamma)
    (hR : 0 ≤ R) :
    ∃ s : ℝ, 0 < s ∧ R < normalizedRate (contractionFromExponent gamma) s := by
  rcases fixed_exponent_overshoots_any_ratio hgamma hR with ⟨s, hs, hovershoot⟩
  refine ⟨s, hs, ?_⟩
  rw [normalizedRate_contraction]
  exact hovershoot

theorem positive_exponent_can_undershoot_any_margin
    {margin : ℝ}
    (hmargin : 0 < margin) :
    ∃ s gamma : ℝ, 0 < s ∧ 0 < gamma ∧ gamma / s < margin := by
  let s : ℝ := margin / 2
  let gamma : ℝ := s ^ 2
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    positivity
  refine ⟨s, gamma, hs, hgamma, ?_⟩
  have hquot : gamma / s = s := by
    dsimp [gamma]
    rw [pow_two, mul_div_cancel_left₀ s (ne_of_gt hs)]
  rw [hquot]
  dsimp [s]
  linarith

#print axioms neg_log_contraction
#print axioms normalizedRate_contraction
#print axioms normalized_rate_window
#print axioms contraction_window_of_exponent_window
#print axioms block_physical_ratio_identity
#print axioms block_decay_window_is_physical_window
#print axioms fixed_exponent_overshoots_any_ratio
#print axioms fixed_contraction_overshoots_any_ratio
#print axioms positive_exponent_can_undershoot_any_margin

end Millennium.YangMills.DobrushinPhysicalScaleWindow
