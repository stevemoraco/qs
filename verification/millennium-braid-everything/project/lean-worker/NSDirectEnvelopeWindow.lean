import Mathlib

namespace NSDirectEnvelopeWindow

/-- Direct isotropic-envelope Fourier exponent in three dimensions. -/
def q (alpha : ℝ) : ℝ := 2 * (alpha - 1) / 3

/-- In the strict physical range, the envelope exponent lies strictly between
`2/3` and `1`. -/
theorem q_lt_one {alpha : ℝ} (h : alpha < 5 / 2) : q alpha < 1 := by
  dsimp [q]
  linarith

/-- The bi-Beltrami direct-envelope upper bound on the adjacent exponent exceeds
one exactly below the `5/2` endpoint. -/
theorem direct_upper_gt_one
    {alpha : ℝ}
    (ha1 : 1 < alpha)
    (ha : alpha < 5 / 2) :
    1 < 3 / (2 * (alpha - 1)) := by
  have hpos : 0 < 2 * (alpha - 1) := by linarith
  apply (lt_div_iff₀ hpos).2
  linarith

/-- Palasek's upper bound exceeds one throughout the viscous range. -/
theorem palasek_upper_gt_one {alpha : ℝ} (ha : 2 < alpha) :
    1 < alpha / 2 := by
  linarith

/-- Abstract existence of a common exponent once both upper bounds exceed one. -/
theorem common_b_exists
    {u v : ℝ}
    (hu : 1 < u)
    (hv : 1 < v) :
    ∃ b : ℝ, 1 < b ∧ b < u ∧ b < v := by
  let m := min u v
  have hm : 1 < m := lt_min hu hv
  refine ⟨(1 + m) / 2, ?_, ?_, ?_⟩
  · linarith
  · have hmu : m ≤ u := min_le_left _ _
    linarith
  · have hmv : m ≤ v := min_le_right _ _
    linarith

/-- Explicit interior arithmetic for `alpha=9/4`, `b=17/16`. -/
theorem explicit_alpha_b_window :
    (1 : ℝ) < 17 / 16 ∧
    (17 / 16 : ℝ) < (9 / 4) / 2 ∧
    (17 / 16 : ℝ) * q (9 / 4) < 1 := by
  norm_num [q]

/-- The explicit defect power is exactly `-11/96`. -/
theorem explicit_defect_exponent :
    (17 / 16 : ℝ) * q (9 / 4) - 1 = -11 / 96 := by
  norm_num [q]

#print axioms q_lt_one
#print axioms direct_upper_gt_one
#print axioms palasek_upper_gt_one
#print axioms common_b_exists
#print axioms explicit_alpha_b_window
#print axioms explicit_defect_exponent

end NSDirectEnvelopeWindow
