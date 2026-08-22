import Mathlib

namespace NSHighFrequencyCoerciveMargin

/-- Positive spectral-strain margin. -/
theorem margin_pos {c K strain : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hstrain : strain < c^2 * K^2) :
    0 < c^2 * K^2 - strain := by
  nlinarith

/-- Reciprocal coercive constant is positive whenever the spectral gap beats strain. -/
theorem inv_margin_pos {c K strain : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hstrain : strain < c^2 * K^2) :
    0 < (c^2 * K^2 - strain)⁻¹ := by
  have h : 0 < c^2 * K^2 - strain := margin_pos hc hK hstrain
  positivity

/-- If the background strain is at most a fixed fraction `q<1` of the
high-frequency Laplacian scale, then the coercive denominator retains the
fraction `1-q` of that scale. -/
theorem fractional_margin {c K strain q : ℝ}
    (hc : 0 <= c) (hK : 0 <= K)
    (hq0 : 0 <= q) (hq1 : q < 1)
    (hstrain : strain <= q * (c^2 * K^2)) :
    (1-q) * (c^2 * K^2) <= c^2 * K^2 - strain := by
  nlinarith [sq_nonneg c, sq_nonneg K]

/-- Concrete half-gap version: if strain is at most half the spectral
Laplacian scale, the inverse denominator is bounded by twice `1/(c²K²)`. -/
theorem half_gap_inverse_bound {c K strain : ℝ}
    (hc : 0 < c) (hK : 0 < K)
    (hstrain : strain <= (1/2 : ℝ) * (c^2 * K^2)) :
    (c^2 * K^2 - strain)⁻¹ <= 2 * (c^2 * K^2)⁻¹ := by
  have hbase : 0 < c^2 * K^2 := by positivity
  have hden : (1/2 : ℝ) * (c^2 * K^2) <= c^2 * K^2 - strain := by
    nlinarith
  have hhalf : 0 < (1/2 : ℝ) * (c^2 * K^2) := by positivity
  have hinv := one_div_le_one_div_of_le hhalf hden
  rw [one_div, one_div] at hinv ⊢
  calc
    (c^2 * K^2 - strain)⁻¹ <= ((1/2 : ℝ) * (c^2 * K^2))⁻¹ := hinv
    _ = 2 * (c^2 * K^2)⁻¹ := by field_simp

#print axioms margin_pos
#print axioms inv_margin_pos
#print axioms fractional_margin
#print axioms half_gap_inverse_bound

end NSHighFrequencyCoerciveMargin
