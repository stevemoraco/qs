import Mathlib

namespace RHPrimePrefixCocycleThreshold

/-- If `m = q - h/L` and `d=L/2`, the squared comparison defect for the
prime-prefix arrival threshold factors exactly through
`h + L^3/(16q)`. -/
theorem squared_defect_factorization
    {q L h m d : ℝ}
    (hq : q ≠ 0)
    (hL : L ≠ 0)
    (hm : m = q - h / L)
    (hd : d = L / 2) :
    (2 * q - m) ^ 2 - (m ^ 2 - d ^ 2) =
      (4 * q / L) * (h + L ^ 3 / (16 * q)) := by
  rw [hm, hd]
  field_simp [hq, hL]
  ring

/-- The unique algebraic zero of the squared defect is the tiny negative
Johnston-kick threshold `-L^3/(16q)`, provided `q,L` are nonzero. -/
theorem squared_defect_zero_iff
    {q L h m d : ℝ}
    (hq : q ≠ 0)
    (hL : L ≠ 0)
    (hm : m = q - h / L)
    (hd : d = L / 2) :
    (2 * q - m) ^ 2 - (m ^ 2 - d ^ 2) = 0 ↔
      h = -(L ^ 3) / (16 * q) := by
  rw [squared_defect_factorization hq hL hm hd]
  constructor
  · intro hz
    have hcoef : 4 * q / L ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hq) hL
    have hsum : h + L ^ 3 / (16 * q) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left hcoef
    calc
      h = (h + L ^ 3 / (16 * q)) - L ^ 3 / (16 * q) := by ring
      _ = -(L ^ 3) / (16 * q) := by rw [hsum]; ring
  · intro hh
    rw [hh]
    field_simp [hq]
    ring

/-- On the physical prime domain `q>0`, `L>0`, the sign of the squared
comparison defect is exactly the sign of the shifted cocycle kick. -/
theorem squared_defect_pos_iff
    {q L h m d : ℝ}
    (hq : 0 < q)
    (hL : 0 < L)
    (hm : m = q - h / L)
    (hd : d = L / 2) :
    0 < (2 * q - m) ^ 2 - (m ^ 2 - d ^ 2) ↔
      -(L ^ 3) / (16 * q) < h := by
  rw [squared_defect_factorization (ne_of_gt hq) (ne_of_gt hL) hm hd]
  have hc : 0 < 4 * q / L := div_pos (mul_pos (by norm_num) hq) hL
  constructor
  · intro hprod
    rcases (mul_pos_iff.mp hprod) with hgood | hbad
    · have hsum : 0 < h + L ^ 3 / (16 * q) := hgood.2
      have hsub : 0 < h - (-(L ^ 3 / (16 * q))) := by
        simpa [sub_neg_eq_add] using hsum
      have hlt : -(L ^ 3 / (16 * q)) < h := sub_pos.mp hsub
      simpa [neg_div] using hlt
    · exact (not_lt_of_ge (le_of_lt hc) hbad.1).elim
  · intro hh
    have hlt : -(L ^ 3 / (16 * q)) < h := by
      simpa [neg_div] using hh
    have hsub : 0 < h - (-(L ^ 3 / (16 * q))) := sub_pos.mpr hlt
    have hsum : 0 < h + L ^ 3 / (16 * q) := by
      simpa [sub_neg_eq_add] using hsub
    exact mul_pos hc hsum

/-- The corresponding negative-sign statement. -/
theorem squared_defect_neg_iff
    {q L h m d : ℝ}
    (hq : 0 < q)
    (hL : 0 < L)
    (hm : m = q - h / L)
    (hd : d = L / 2) :
    (2 * q - m) ^ 2 - (m ^ 2 - d ^ 2) < 0 ↔
      h < -(L ^ 3) / (16 * q) := by
  rw [squared_defect_factorization (ne_of_gt hq) (ne_of_gt hL) hm hd]
  have hc : 0 < 4 * q / L := div_pos (mul_pos (by norm_num) hq) hL
  constructor
  · intro hprod
    rcases (mul_neg_iff.mp hprod) with hgood | hbad
    · have hsum : h + L ^ 3 / (16 * q) < 0 := hgood.2
      have hsub : h - (-(L ^ 3 / (16 * q))) < 0 := by
        simpa [sub_neg_eq_add] using hsum
      have hlt : h < -(L ^ 3 / (16 * q)) := sub_neg.mp hsub
      simpa [neg_div] using hlt
    · exact (not_lt_of_ge (le_of_lt hc) hbad.1).elim
  · intro hh
    have hlt : h < -(L ^ 3 / (16 * q)) := by
      simpa [neg_div] using hh
    have hsub : h - (-(L ^ 3 / (16 * q))) < 0 := sub_neg.mpr hlt
    have hsum : h + L ^ 3 / (16 * q) < 0 := by
      simpa [sub_neg_eq_add] using hsub
    exact mul_neg_of_pos_of_neg hc hsum

#print axioms squared_defect_factorization
#print axioms squared_defect_zero_iff
#print axioms squared_defect_pos_iff
#print axioms squared_defect_neg_iff

end RHPrimePrefixCocycleThreshold
