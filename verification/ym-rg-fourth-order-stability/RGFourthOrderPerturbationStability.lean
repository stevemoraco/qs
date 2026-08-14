import Mathlib

/-!
# Fourth-order RG perturbation stability

Finite firewall for the two-loop dimensional-transmutation normalization bridge.
For an exact cubic weak-coupling step plus a remainder `r = O(u^4)`, this file
shows that (under an explicit smallness hypothesis) the perturbed coupling
stays positive, retains quadratic growth, and changes the two-loop corrected
coordinate by only `O(u^2)` relative to the exact cubic step.

Honesty boundary: this is a scalar finite theorem. It does not prove that any
Yang--Mills blocking transformation has an `O(u^4)` remainder, does not identify
the coefficients with a specific renormalization scheme, and does not prove
Osterwalder--Schrader reconstruction or a physical mass gap.
-/

namespace Millennium.YangMills

/-- Exact cubic reference step. -/
def fourthOrderReferenceStep (b c u : ℝ) : ℝ :=
  u * (1 + b * u + c * u^2)

/-- Cubic step perturbed by an arbitrary scalar remainder. -/
def fourthOrderPerturbedStep (b c u r : ℝ) : ℝ :=
  fourthOrderReferenceStep b c u + r

/-- Two-loop corrected inverse-coupling coordinate. -/
noncomputable def fourthOrderCorrectedCoordinate (b c u : ℝ) : ℝ :=
  1 / (b * u) + (c / b^2 - 1) * Real.log u

/-- `log` is Lipschitz on a positive half-line, with the elementary reciprocal
lower-bound constant. -/
theorem abs_log_sub_log_le_of_lower_bound
    (x y m : ℝ) (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log y - Real.log x| ≤ (1 / m) * |y - x| := by
  have hder : ∀ z ∈ Set.Ici m,
      HasDerivWithinAt Real.log z⁻¹ (Set.Ici m) z := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hm hz
    exact (Real.hasDerivAt_log (ne_of_gt hzpos)).hasDerivWithinAt
  have hbound : ∀ z ∈ Set.Ici m, ‖z⁻¹‖ ≤ 1 / m := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hm hz
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzpos), one_div]
    exact (inv_le_inv₀ hzpos hm).2 hz
  have h := (convex_Ici m).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound hx hy
  simpa [Real.norm_eq_abs] using h

/-- The exact cubic reference step is at least the incoming positive coupling. -/
theorem referenceStep_ge_input
    (b c u : ℝ) (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u) :
    u ≤ fourthOrderReferenceStep b c u := by
  unfold fourthOrderReferenceStep
  have hbu2 : 0 ≤ b * u^2 := mul_nonneg (le_of_lt hb) (sq_nonneg u)
  have hcu3 : 0 ≤ c * u^3 := by positivity
  nlinarith

/-- An `O(u^4)` perturbation cannot push a positive cubic step below `u/2`
when its dimensionless size satisfies `R u^3 ≤ 1/2`. -/
theorem perturbedStep_ge_half_input
    (b c R u r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u)
    (hrem : |r| ≤ R * u^4)
    (hsmall : R * u^3 ≤ 1 / 2) :
    u / 2 ≤ fourthOrderPerturbedStep b c u r := by
  have href := referenceStep_ge_input b c u hb hc hu
  have hrlo : -(R * u^4) ≤ r := (abs_le.mp hrem).1
  have hRu4 : R * u^4 ≤ u / 2 := by
    calc
      R * u^4 = (R * u^3) * u := by ring
      _ ≤ (1 / 2) * u := mul_le_mul_of_nonneg_right hsmall (le_of_lt hu)
      _ = u / 2 := by ring
  unfold fourthOrderPerturbedStep
  linarith

/-- Under the second explicit smallness condition, the perturbed step still
has a uniform quadratic growth floor. -/
theorem perturbedStep_quadratic_growth
    (b c R u r : ℝ)
    (hc : 0 ≤ c) (hu : 0 < u)
    (hrem : |r| ≤ R * u^4)
    (hsmall : R * u^2 ≤ b / 2) :
    (b / 2) * u^2 ≤ fourthOrderPerturbedStep b c u r - u := by
  have hrlo : -(R * u^4) ≤ r := (abs_le.mp hrem).1
  have hRu4 : R * u^4 ≤ (b / 2) * u^2 := by
    calc
      R * u^4 = (R * u^2) * u^2 := by ring
      _ ≤ (b / 2) * u^2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg u)
  have hcu3 : 0 ≤ c * u^3 := by positivity
  unfold fourthOrderPerturbedStep fourthOrderReferenceStep
  nlinarith

/-- Reciprocal part of the corrected coordinate is stable under the fourth-order
perturbation. The constant is coarse but summable. -/
theorem reciprocal_coordinate_perturbation_le
    (b R u w v r : ℝ)
    (hb : 0 < b) (hR : 0 ≤ R) (hu : 0 < u)
    (hw : u ≤ w) (hv : u / 2 ≤ v)
    (hvr : v = w + r) (hrem : |r| ≤ R * u^4) :
    |1 / (b * v) - 1 / (b * w)| ≤ (2 * R / b) * u^2 := by
  have hwpos : 0 < w := lt_of_lt_of_le hu hw
  have hvpos : 0 < v := lt_of_lt_of_le (half_pos hu) hv
  have hden : 0 < b * v * w := mul_pos (mul_pos hb hvpos) hwpos
  have hprod1 : (u / 2) * u ≤ (u / 2) * w :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have hprod2 : (u / 2) * w ≤ v * w :=
    mul_le_mul_of_nonneg_right hv (le_of_lt hwpos)
  have hprod : u^2 ≤ 2 * (v * w) := by
    nlinarith [hprod1, hprod2]
  have hscaled : R * u^4 ≤ 2 * R * u^2 * (v * w) := by
    have := mul_le_mul_of_nonneg_left hprod (mul_nonneg hR (sq_nonneg u))
    nlinarith
  have hnum : |w - v| ≤ R * u^4 := by
    rw [hvr]
    simpa [abs_neg] using hrem
  have hid : 1 / (b * v) - 1 / (b * w) = (w - v) / (b * v * w) := by
    field_simp [ne_of_gt hb, ne_of_gt hvpos, ne_of_gt hwpos]
  rw [hid, abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  have hbne : b ≠ 0 := ne_of_gt hb
  calc
    |w - v| ≤ R * u^4 := hnum
    _ ≤ 2 * R * u^2 * (v * w) := hscaled
    _ = ((2 * R / b) * u^2) * (b * v * w) := by
      field_simp [hbne]

/-- Logarithmic part of the corrected coordinate is stable under the same
fourth-order perturbation. -/
theorem log_coordinate_perturbation_le
    (R u w v r : ℝ)
    (hu : 0 < u)
    (hw : u ≤ w) (hv : u / 2 ≤ v)
    (hvr : v = w + r) (hrem : |r| ≤ R * u^4) :
    |Real.log v - Real.log w| ≤ 2 * R * u^3 := by
  have hlog := abs_log_sub_log_le_of_lower_bound w v (u / 2)
      (half_pos hu) (by linarith) hv
  have hdiff : |v - w| = |r| := by rw [hvr]; ring_nf
  rw [hdiff] at hlog
  calc
    |Real.log v - Real.log w| ≤ (1 / (u / 2)) * |r| := hlog
    _ ≤ (1 / (u / 2)) * (R * u^4) := by
      exact mul_le_mul_of_nonneg_left hrem (by positivity)
    _ = 2 * R * u^3 := by
      field_simp [ne_of_gt hu]

/-- Main local fourth-order stability theorem. An `O(u^4)` perturbation of the
cubic recurrence changes the two-loop corrected coordinate by only `O(u^2)`.
The `U` parameter is a fixed weak-coupling ceiling used only to turn the
logarithmic `u^3` contribution into a quadratic bound. -/
theorem correctedCoordinate_perturbation_le_quadratic
    (b c R u U r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hu : 0 < u) (huU : u ≤ U)
    (hrem : |r| ≤ R * u^4)
    (hsmall : R * u^3 ≤ 1 / 2) :
    |fourthOrderCorrectedCoordinate b c
        (fourthOrderPerturbedStep b c u r)
      - fourthOrderCorrectedCoordinate b c
        (fourthOrderReferenceStep b c u)|
      ≤ (2 * R / b + 2 * |c / b^2 - 1| * R * U) * u^2 := by
  let w := fourthOrderReferenceStep b c u
  let v := fourthOrderPerturbedStep b c u r
  have hw : u ≤ w := by
    simpa [w] using referenceStep_ge_input b c u hb hc hu
  have hv : u / 2 ≤ v := by
    simpa [v] using perturbedStep_ge_half_input b c R u r hb hc hu hrem hsmall
  have hvr : v = w + r := by
    simp [v, w, fourthOrderPerturbedStep]
  have hrec := reciprocal_coordinate_perturbation_le
      b R u w v r hb hR hu hw hv hvr hrem
  have hlog := log_coordinate_perturbation_le
      R u w v r hu hw hv hvr hrem
  unfold fourthOrderCorrectedCoordinate
  dsimp [w, v] at hrec hlog ⊢
  calc
    |(1 / (b * fourthOrderPerturbedStep b c u r) +
          (c / b^2 - 1) * Real.log (fourthOrderPerturbedStep b c u r)) -
        (1 / (b * fourthOrderReferenceStep b c u) +
          (c / b^2 - 1) * Real.log (fourthOrderReferenceStep b c u))|
      ≤ |1 / (b * fourthOrderPerturbedStep b c u r) -
            1 / (b * fourthOrderReferenceStep b c u)|
        + |(c / b^2 - 1) *
            (Real.log (fourthOrderPerturbedStep b c u r) -
              Real.log (fourthOrderReferenceStep b c u))| := by
          have hdecomp :
              (1 / (b * fourthOrderPerturbedStep b c u r) +
                  (c / b^2 - 1) * Real.log (fourthOrderPerturbedStep b c u r)) -
                (1 / (b * fourthOrderReferenceStep b c u) +
                  (c / b^2 - 1) * Real.log (fourthOrderReferenceStep b c u)) =
              (1 / (b * fourthOrderPerturbedStep b c u r) -
                  1 / (b * fourthOrderReferenceStep b c u)) +
                (c / b^2 - 1) *
                  (Real.log (fourthOrderPerturbedStep b c u r) -
                    Real.log (fourthOrderReferenceStep b c u)) := by ring
          rw [hdecomp]
          exact abs_add_le _ _
    _ ≤ (2 * R / b) * u^2 +
          |c / b^2 - 1| * (2 * R * u^3) := by
          rw [abs_mul]
          exact add_le_add hrec
            (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
    _ ≤ (2 * R / b) * u^2 +
          |c / b^2 - 1| * (2 * R * U * u^2) := by
          have hu3 : u^3 ≤ U * u^2 := by
            nlinarith [sq_nonneg u]
          have hcoef : 0 ≤ 2 * R := by positivity
          have htmp : 2 * R * u^3 ≤ 2 * R * U * u^2 := by
            have := mul_le_mul_of_nonneg_left hu3 hcoef
            nlinarith
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left htmp (abs_nonneg _))
    _ = (2 * R / b + 2 * |c / b^2 - 1| * R * U) * u^2 := by
          ring

#print axioms abs_log_sub_log_le_of_lower_bound
#print axioms referenceStep_ge_input
#print axioms perturbedStep_ge_half_input
#print axioms perturbedStep_quadratic_growth
#print axioms reciprocal_coordinate_perturbation_le
#print axioms log_coordinate_perturbation_le
#print axioms correctedCoordinate_perturbation_le_quadratic

end Millennium.YangMills
