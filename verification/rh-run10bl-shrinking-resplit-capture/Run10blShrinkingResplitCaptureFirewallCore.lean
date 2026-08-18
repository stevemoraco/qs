import Mathlib

namespace Millennium.RH

/-- Equal-weight average over the independent four-atom sign model
`A=±r`, `B=±s`. -/
noncomputable def run10blAvg4
    (f : ℝ → ℝ → ℝ) (r s : ℝ) : ℝ :=
  (f r s + f r (-s) + f (-r) s + f (-r) (-s)) / 4

/-- The two-square localizer with the shifts set equal to the two RMS scales. -/
noncomputable def run10blWeight
    (r s A B : ℝ) : ℝ :=
  (A + r) ^ 2 * (B + s) ^ 2

/-- The four-atom short block is centered. -/
theorem run10bl_avg_A (r s : ℝ) :
    run10blAvg4 (fun A _ => A) r s = 0 := by
  unfold run10blAvg4
  ring

/-- The four-atom long block is centered. -/
theorem run10bl_avg_B (r s : ℝ) :
    run10blAvg4 (fun _ B => B) r s = 0 := by
  unfold run10blAvg4
  ring

/-- Exact short-block variance. -/
theorem run10bl_avg_A_sq (r s : ℝ) :
    run10blAvg4 (fun A _ => A ^ 2) r s = r ^ 2 := by
  unfold run10blAvg4
  ring

/-- Exact long-block variance. -/
theorem run10bl_avg_B_sq (r s : ℝ) :
    run10blAvg4 (fun _ B => B ^ 2) r s = s ^ 2 := by
  unfold run10blAvg4
  ring

/-- The short-block cubic moment vanishes exactly. -/
theorem run10bl_avg_A_cube (r s : ℝ) :
    run10blAvg4 (fun A _ => A ^ 3) r s = 0 := by
  unfold run10blAvg4
  ring

/-- The long-block cubic moment vanishes exactly. -/
theorem run10bl_avg_B_cube (r s : ℝ) :
    run10blAvg4 (fun _ B => B ^ 3) r s = 0 := by
  unfold run10blAvg4
  ring

/-- With RMS shifts, the localizer is supported only on the `(+,+)` atom. -/
theorem run10bl_weight_mass (r s : ℝ) :
    run10blAvg4 (fun A B => run10blWeight r s A B) r s =
      4 * r ^ 2 * s ^ 2 := by
  unfold run10blAvg4 run10blWeight
  ring

/-- The same four-atom model saturates the Run10bj weighted-tilt ceiling. -/
theorem run10bl_weighted_tilt_saturates (r s : ℝ) :
    run10blAvg4
        (fun A B => (A + B) * run10blWeight r s A B) r s =
      (r + s) * (4 * r ^ 2 * s ^ 2) := by
  unfold run10blAvg4 run10blWeight
  ring

/-- Exact cap-witness mean in the sharp four-atom model. -/
theorem run10bl_cap_mean_exact (r s q : ℝ) :
    run10blAvg4
        (fun A B => (q - A - B) * run10blWeight r s A B) r s =
      (q - r - s) * (4 * r ^ 2 * s ^ 2) := by
  unfold run10blAvg4 run10blWeight
  ring

/-- Any cap below the top atom has strictly negative weighted mean when both
block scales are nonzero. -/
theorem run10bl_cap_mean_negative
    (r s q : ℝ)
    (hr : 0 < r)
    (hs : 0 < s)
    (hq : q < r + s) :
    run10blAvg4
        (fun A B => (q - A - B) * run10blWeight r s A B) r s < 0 := by
  rw [run10bl_cap_mean_exact]
  have hm : 0 < 4 * r ^ 2 * s ^ 2 := by
    positivity
  have hneg : q - r - s < 0 := by
    linarith
  exact mul_neg_of_neg_of_pos hneg hm

/-- Under the shrinking-split ordering, only the `(+,+)` atom lies above one,
so the equal-weight mean squared positive excess is exactly one quarter of the
top excess squared. -/
theorem run10bl_four_atom_excess_square
    (r s : ℝ)
    (hr0 : 0 ≤ r)
    (hrs : r ≤ s)
    (hs1 : s ≤ 1)
    (hone : 1 ≤ r + s) :
    ((max (r + s - 1) 0) ^ 2 +
        (max (r - s - 1) 0) ^ 2 +
        (max (-r + s - 1) 0) ^ 2 +
        (max (-r - s - 1) 0) ^ 2) / 4 =
      (r + s - 1) ^ 2 / 4 := by
  have hs0 : 0 ≤ s := le_trans hr0 hrs
  have hpp : 0 ≤ r + s - 1 := by linarith
  have hpm : r - s - 1 ≤ 0 := by linarith
  have hmp : -r + s - 1 ≤ 0 := by linarith
  have hmm : -r - s - 1 ≤ 0 := by linarith
  rw [max_eq_left hpp]
  rw [max_eq_right hpm]
  rw [max_eq_right hmp]
  rw [max_eq_right hmm]
  ring

/-- The complete squared positive-excess currency of the four-atom shell is at
most `r^2/4`; this is the finite quadratic collapse behind Run10bl. -/
theorem run10bl_excess_square_le_short_scale
    (r s : ℝ)
    (hr0 : 0 ≤ r)
    (hs1 : s ≤ 1)
    (hone : 1 ≤ r + s) :
    (r + s - 1) ^ 2 / 4 ≤ r ^ 2 / 4 := by
  have hg0 : 0 ≤ r + s - 1 := by linarith
  have hgr : r + s - 1 ≤ r := by linarith
  have hsum : 0 ≤ r + (r + s - 1) := add_nonneg hr0 hg0
  have hprod :
      0 ≤ (r - (r + s - 1)) * (r + (r + s - 1)) := by
    exact mul_nonneg (sub_nonneg.mpr hgr) hsum
  nlinarith

/-- Multiplying by any nonnegative Suzuki scale `a` preserves the collapse:
the threshold-only capture currency is bounded by `a*r^2/4`. -/
theorem run10bl_scaled_excess_square_le_short_scale
    (a r s : ℝ)
    (ha : 0 ≤ a)
    (hr0 : 0 ≤ r)
    (hs1 : s ≤ 1)
    (hone : 1 ≤ r + s) :
    a * ((r + s - 1) ^ 2 / 4) ≤ a * (r ^ 2 / 4) := by
  exact mul_le_mul_of_nonneg_left
    (run10bl_excess_square_le_short_scale r s hr0 hs1 hone) ha

/-- Rational Pythagorean short scale used for an exact shrinking family. -/
noncomputable def run10blR (t : ℝ) : ℝ :=
  2 * t / (1 + t ^ 2)

/-- Rational Pythagorean long scale used for an exact shrinking family. -/
noncomputable def run10blS (t : ℝ) : ℝ :=
  (1 - t ^ 2) / (1 + t ^ 2)

/-- The rational family has exact unit total variance. -/
theorem run10bl_pythagorean_unit_variance (t : ℝ) :
    run10blR t ^ 2 + run10blS t ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  unfold run10blR run10blS
  field_simp [hden]
  ring

/-- In the rational family the top excess is exactly `(1-t)` times the short
scale, so its squared weak-tail currency is quadratically small as `t→0`. -/
theorem run10bl_pythagorean_gap (t : ℝ) :
    run10blR t + run10blS t - 1 = (1 - t) * run10blR t := by
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  unfold run10blR run10blS
  field_simp [hden]
  ring

#check run10blAvg4
#check run10blWeight
#check run10bl_avg_A
#print axioms run10bl_avg_A
#check run10bl_avg_B
#print axioms run10bl_avg_B
#check run10bl_avg_A_sq
#print axioms run10bl_avg_A_sq
#check run10bl_avg_B_sq
#print axioms run10bl_avg_B_sq
#check run10bl_avg_A_cube
#print axioms run10bl_avg_A_cube
#check run10bl_avg_B_cube
#print axioms run10bl_avg_B_cube
#check run10bl_weight_mass
#print axioms run10bl_weight_mass
#check run10bl_weighted_tilt_saturates
#print axioms run10bl_weighted_tilt_saturates
#check run10bl_cap_mean_exact
#print axioms run10bl_cap_mean_exact
#check run10bl_cap_mean_negative
#print axioms run10bl_cap_mean_negative
#check run10bl_four_atom_excess_square
#print axioms run10bl_four_atom_excess_square
#check run10bl_excess_square_le_short_scale
#print axioms run10bl_excess_square_le_short_scale
#check run10bl_scaled_excess_square_le_short_scale
#print axioms run10bl_scaled_excess_square_le_short_scale
#check run10bl_pythagorean_unit_variance
#print axioms run10bl_pythagorean_unit_variance
#check run10bl_pythagorean_gap
#print axioms run10bl_pythagorean_gap

end Millennium.RH
