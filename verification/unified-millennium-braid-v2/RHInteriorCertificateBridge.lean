import Mathlib

namespace Millennium.RH.InteriorCertificate

def q (y : ℝ) : ℝ := 4 * y^2 - 2 * y

noncomputable def stationaryY (N : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * N)) / 4

theorem stationaryY_quadratic (N : ℝ) (hN : 0 ≤ N) : q (stationaryY N) = N := by
  have hrad : 0 ≤ 1 + 4 * N := by linarith
  have hs : (Real.sqrt (1 + 4 * N)) ^ 2 = 1 + 4 * N := by simpa using Real.sq_sqrt hrad
  dsimp [q, stationaryY]
  nlinarith

theorem quarter_lt_stationaryY (N : ℝ) (hN : 0 ≤ N) : (1 / 4 : ℝ) < stationaryY N := by
  have hrad : 0 < 1 + 4 * N := by linarith
  have hs : 0 < Real.sqrt (1 + 4 * N) := Real.sqrt_pos.2 hrad
  dsimp [stationaryY]
  nlinarith

theorem q_lt_q {a b : ℝ} (ha : (1 / 4 : ℝ) < a) (hab : a < b) : q a < q b := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hfac : 0 < 4 * (a + b) - 2 := by linarith
  have hprod : 0 < (b - a) * (4 * (a + b) - 2) := mul_pos hba hfac
  dsimp [q]
  nlinarith [hprod]

theorem q_lt_iff {a b : ℝ} (ha : (1 / 4 : ℝ) < a) (hb : (1 / 4 : ℝ) < b) : q a < q b ↔ a < b := by
  constructor
  · intro hq
    by_contra hnot
    have hba : b ≤ a := le_of_not_gt hnot
    rcases lt_or_eq_of_le hba with hlt | heq
    · have hrev : q b < q a := q_lt_q hb hlt
      linarith
    · subst a
      exact (lt_irrefl (q b)) hq
  · intro hab
    exact q_lt_q ha hab

theorem stationaryY_band_iff (N a b : ℝ) (hN : 0 ≤ N) (ha : (1 / 4 : ℝ) < a) (hab : a < b) :
    (a < stationaryY N ∧ stationaryY N < b) ↔ (q a < N ∧ N < q b) := by
  have hy : (1 / 4 : ℝ) < stationaryY N := quarter_lt_stationaryY N hN
  have hb : (1 / 4 : ℝ) < b := by linarith
  have hquad : q (stationaryY N) = N := stationaryY_quadratic N hN
  constructor
  · rintro ⟨hay, hyb⟩
    constructor
    · calc q a < q (stationaryY N) := (q_lt_iff ha hy).2 hay
           _ = N := hquad
    · calc N = q (stationaryY N) := hquad.symm
           _ < q b := (q_lt_iff hy hb).2 hyb
  · rintro ⟨hqa, hqb⟩
    constructor
    · apply (q_lt_iff ha hy).1
      calc q a < N := hqa
           _ = q (stationaryY N) := hquad.symm
    · apply (q_lt_iff hy hb).1
      calc q (stationaryY N) = N := hquad
           _ < q b := hqb

theorem quadratic_model_margin_transfer {target L G d μ h : ℝ}
    (hμ : 0 < μ)
    (hmodel : L - d * h + (μ / 2) * h ^ 2 ≤ G)
    (hmargin : target + d ^ 2 / (2 * μ) ≤ L) : target ≤ G := by
  have htwo : 0 < 2 * μ := by positivity
  have hdrop : L - G ≤ d * h - (μ / 2) * h ^ 2 := by linarith
  have hquad : d * h - (μ / 2) * h ^ 2 ≤ d ^ 2 / (2 * μ) := by
    apply (le_div_iff₀ htwo).2
    nlinarith [sq_nonneg (μ * h - d)]
  linarith

theorem interior_certificate {N a b target L G d μ h : ℝ}
    (hN : 0 ≤ N) (ha : (1 / 4 : ℝ) < a) (hab : a < b)
    (hband : q a < N ∧ N < q b) (hμ : 0 < μ)
    (hmodel : L - d * h + (μ / 2) * h ^ 2 ≤ G)
    (hmargin : target + d ^ 2 / (2 * μ) ≤ L) :
    (a < stationaryY N ∧ stationaryY N < b) ∧ target ≤ G := by
  constructor
  · exact (stationaryY_band_iff N a b hN ha hab).2 hband
  · exact quadratic_model_margin_transfer hμ hmodel hmargin

#print axioms stationaryY_band_iff
#print axioms quadratic_model_margin_transfer
#print axioms interior_certificate

end Millennium.RH.InteriorCertificate
