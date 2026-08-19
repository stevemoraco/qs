import Mathlib

namespace Millennium.RH

/-- Self-contained copy of the exact chord identity needed to replay the
Run10bmB first-split lower bound inside this standalone verifier source. -/
theorem run10bo_chord_decomposition (alpha : ℝ) :
    (((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - alpha) ^ 2) -
        4 * alpha ^ 2 * (1 - 2 * alpha)) =
      (40401 - 2432918 * alpha) / 100000000 +
        alpha * (5000 * alpha - 83) * (80000 * alpha - 38873) /
          50000000 := by
  ring

/-- Standalone replay of the banked Run10bmB consequence: the literal
`101/100` determinant crossing on a natural one-`AB` root forces the first
support split above `83/5000`. -/
theorem run10bo_crossing_forces_first_split
    (alpha beta rB : ℝ)
    (ha : 0 ≤ alpha)
    (hb : 0 ≤ beta)
    (hnatural : alpha + beta ≤ 1)
    (hrB : rB ^ 2 = beta ^ 2 - alpha ^ 2)
    (hdet :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) <
        4 * alpha ^ 2 * rB ^ 2) :
    (83 / 5000 : ℝ) < alpha := by
  have hbeta : beta ≤ 1 - alpha := by
    linarith
  have honealpha : 0 ≤ 1 - alpha := by
    linarith
  have hbeta2 : beta ^ 2 ≤ (1 - alpha) ^ 2 := by
    nlinarith
  have hrBupper : rB ^ 2 ≤ 1 - 2 * alpha := by
    rw [hrB]
    nlinarith [hbeta2]
  have hqpos : 0 ≤ (101 / 100 : ℝ) ^ 2 - 1 := by
    norm_num
  have hlower :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - alpha) ^ 2) ≤
        ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hqpos
    nlinarith [hbeta2]
  have ha2 : 0 ≤ 4 * alpha ^ 2 := by
    positivity
  have hupper :
      4 * alpha ^ 2 * rB ^ 2 ≤
        4 * alpha ^ 2 * (1 - 2 * alpha) := by
    exact mul_le_mul_of_nonneg_left hrBupper ha2
  have hboundaryneg :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - alpha) ^ 2) -
        4 * alpha ^ 2 * (1 - 2 * alpha) < 0 := by
    linarith
  by_contra hnot
  have hac : alpha ≤ (83 / 5000 : ℝ) := by
    exact le_of_not_gt hnot
  have hf1 : 5000 * alpha - 83 ≤ 0 := by
    nlinarith
  have hf2 : 80000 * alpha - 38873 ≤ 0 := by
    nlinarith
  have hpairs :
      0 ≤ (5000 * alpha - 83) * (80000 * alpha - 38873) := by
    exact mul_nonneg_of_nonpos_of_nonpos hf1 hf2
  have hprod :
      0 ≤ alpha * ((5000 * alpha - 83) * (80000 * alpha - 38873)) := by
    exact mul_nonneg ha hpairs
  have hlinear : 0 < 40401 - 2432918 * alpha := by
    have hc : (0 : ℝ) < 36403 / 2500 := by
      norm_num
    nlinarith
  rw [run10bo_chord_decomposition alpha] at hboundaryneg
  have hterm :
      0 ≤ alpha * (5000 * alpha - 83) * (80000 * alpha - 38873) /
        50000000 := by
    have hprod' :
        0 ≤ alpha * (5000 * alpha - 83) * (80000 * alpha - 38873) := by
      simpa [mul_assoc] using hprod
    exact div_nonneg hprod' (by norm_num)
  have hline :
      0 < (40401 - 2432918 * alpha) / 100000000 := by
    exact div_pos hlinear (by norm_num)
  linarith

/-- In the one-`AB` natural-root crossing geometry, tuning the first split cannot
push every unavoidable signed top row back to natural length. Once the
`101/100` determinant crossing holds, either the `ABC^2` support scale
`1+alpha` already exceeds `1.0332`, or both sides of the `A^2B^2C` resonant
partition exceed `1.0332`.

This is finite scalar support arithmetic only. The interpretation in terms of
specific signed prime monomials uses the parent source typing and is not encoded
as an analytic or RH assumption here. -/
theorem run10bo_crossing_forces_threepercent_signed_overflow
    (alpha beta rB : ℝ)
    (ha : 0 ≤ alpha)
    (hb : 0 ≤ beta)
    (hnatural : alpha + beta ≤ 1)
    (hrB : rB ^ 2 = beta ^ 2 - alpha ^ 2)
    (hdet :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) <
        4 * alpha ^ 2 * rB ^ 2) :
    (2583 / 2500 : ℝ) < 1 + alpha ∨
      ((2583 / 2500 : ℝ) < 1 + 2 * alpha ∧
       (2583 / 2500 : ℝ) < 2 * beta) := by
  have halpha : (83 / 5000 : ℝ) < alpha :=
    run10bo_crossing_forces_first_split
      alpha beta rB ha hb hnatural hrB hdet
  by_cases hbig : (166 / 5000 : ℝ) ≤ alpha
  · left
    linarith
  · right
    have halphaUpper : alpha < (166 / 5000 : ℝ) := lt_of_not_ge hbig
    constructor
    · linarith
    · by_contra hbetaNot
      have h2beta : 2 * beta ≤ (2583 / 2500 : ℝ) :=
        le_of_not_gt hbetaNot
      have hbetaUpper : beta ≤ (2583 / 5000 : ℝ) := by
        linarith
      have hbetaSq : beta ^ 2 ≤ (2583 / 5000 : ℝ) ^ 2 := by
        nlinarith
      have halphaSq : alpha ^ 2 ≤ (166 / 5000 : ℝ) ^ 2 := by
        nlinarith
      have hrBUpper : rB ^ 2 ≤ (2583 / 5000 : ℝ) ^ 2 := by
        rw [hrB]
        nlinarith [sq_nonneg alpha]
      have hleftLower :
          ((101 / 100 : ℝ) ^ 2 - 1) *
              ((101 / 100 : ℝ) ^ 2 - (2583 / 5000 : ℝ) ^ 2) ≤
            ((101 / 100 : ℝ) ^ 2 - 1) *
              ((101 / 100 : ℝ) ^ 2 - beta ^ 2) := by
        have hq : 0 ≤ (101 / 100 : ℝ) ^ 2 - 1 := by
          norm_num
        exact mul_le_mul_of_nonneg_left (by nlinarith [hbetaSq]) hq
      have hprod :
          alpha ^ 2 * rB ^ 2 ≤
            (166 / 5000 : ℝ) ^ 2 * (2583 / 5000 : ℝ) ^ 2 := by
        calc
          alpha ^ 2 * rB ^ 2 ≤
              (166 / 5000 : ℝ) ^ 2 * rB ^ 2 :=
            mul_le_mul_of_nonneg_right halphaSq (sq_nonneg rB)
          _ ≤ (166 / 5000 : ℝ) ^ 2 * (2583 / 5000 : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hrBUpper (by positivity)
      have hrightUpper :
          4 * alpha ^ 2 * rB ^ 2 ≤
            4 * (166 / 5000 : ℝ) ^ 2 * (2583 / 5000 : ℝ) ^ 2 := by
        nlinarith
      have hconstantGap :
          4 * (166 / 5000 : ℝ) ^ 2 * (2583 / 5000 : ℝ) ^ 2 <
            ((101 / 100 : ℝ) ^ 2 - 1) *
              ((101 / 100 : ℝ) ^ 2 - (2583 / 5000 : ℝ) ^ 2) := by
        norm_num
      linarith

/-- Low-first-split specialization: if `alpha<0.0332`, the two support ceilings
for the unavoidable `A^2B^2C` partition are both strictly beyond `1.0332`. -/
theorem run10bo_low_split_A2B2C_floor
    (alpha beta rB : ℝ)
    (ha : 0 ≤ alpha)
    (hb : 0 ≤ beta)
    (hnatural : alpha + beta ≤ 1)
    (hrB : rB ^ 2 = beta ^ 2 - alpha ^ 2)
    (hdet :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) <
        4 * alpha ^ 2 * rB ^ 2)
    (halphaUpper : alpha < (166 / 5000 : ℝ)) :
    (2583 / 2500 : ℝ) < min (1 + 2 * alpha) (2 * beta) := by
  have h := run10bo_crossing_forces_threepercent_signed_overflow
    alpha beta rB ha hb hnatural hrB hdet
  rcases h with hhigh | hlow
  · linarith
  · exact lt_min hlow.1 hlow.2

/-- The universal lower threshold is exactly `1.0332`. -/
theorem run10bo_threepercent_threshold_exact :
    (1 : ℝ) + 2 * (83 / 5000 : ℝ) = 2583 / 2500 := by
  norm_num

#print axioms run10bo_chord_decomposition
#print axioms run10bo_crossing_forces_first_split
#print axioms run10bo_crossing_forces_threepercent_signed_overflow
#print axioms run10bo_low_split_A2B2C_floor
#print axioms run10bo_threepercent_threshold_exact

end Millennium.RH
