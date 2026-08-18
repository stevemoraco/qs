import Mathlib

namespace Millennium.RH

/--
Two-block square-localizer mass when the actual centered block variances are
`u,v` and the square shifts are `c,d`.
-/
noncomputable def run10bkMass (u v c d : ℝ) : ℝ :=
  (c ^ 2 + u) * (d ^ 2 + v)

/--
The corresponding ideal first tilted moment under zero first/third block
moments and factorization.
-/
noncomputable def run10bkTilt (u v c d : ℝ) : ℝ :=
  2 * c * u * (d ^ 2 + v) +
  2 * d * v * (c ^ 2 + u)

/--
Exact lower-tilt identity.  If the actual variances dominate the squared
chosen shifts, each block contributes at least its shift to the weighted tilt.
-/
theorem run10bk_lower_tilt_identity
    (u v c d : ℝ) :
    run10bkTilt u v c d - (c + d) * run10bkMass u v c d =
      c * (u - c ^ 2) * (d ^ 2 + v) +
      d * (v - d ^ 2) * (c ^ 2 + u) := by
  unfold run10bkMass run10bkTilt
  ring

/--
Variance lower bounds turn the exact identity into the denominator-free score
bound `(c+d) M0 <= M1`.
-/
theorem run10bk_shift_sum_mass_le_tilt
    (u v c d : ℝ)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (huc : c ^ 2 ≤ u)
    (hvd : d ^ 2 ≤ v) :
    (c + d) * run10bkMass u v c d ≤ run10bkTilt u v c d := by
  have hv : 0 ≤ v := le_trans (sq_nonneg d) hvd
  have hu : 0 ≤ u := le_trans (sq_nonneg c) huc
  have huv : 0 ≤ d ^ 2 + v := add_nonneg (sq_nonneg d) hv
  have huu : 0 ≤ c ^ 2 + u := add_nonneg (sq_nonneg c) hu
  have h1 : 0 ≤ c * (u - c ^ 2) * (d ^ 2 + v) := by
    exact mul_nonneg (mul_nonneg hc (sub_nonneg.mpr huc)) huv
  have h2 : 0 ≤ d * (v - d ^ 2) * (c ^ 2 + u) := by
    exact mul_nonneg (mul_nonneg hd (sub_nonneg.mpr hvd)) huu
  rw [← sub_nonneg]
  rw [run10bk_lower_tilt_identity]
  exact add_nonneg h1 h2

/--
The explicit source-safety arithmetic for the robust one-percent split:
`alpha=1/90`, low shift `1/91`, high shift `4999/5000`, and raised cap
`2021/2000`.
-/
theorem run10bk_rational_resplit_margins :
    (1 / 91 : ℝ) ^ 2 < (1 / 90 : ℝ) ^ 2 ∧
    (4999 / 5000 : ℝ) ^ 2 < 1 - (1 / 90 : ℝ) ^ 2 ∧
    (2021 / 2000 : ℝ) < (1 / 91 : ℝ) + (4999 / 5000 : ℝ) := by
  norm_num

/--
Once the two physical-window variances clear the explicit rational floors,
the raised-cap prime-only two-square witness has strictly negative mean.
This is finite real algebra only; it does not establish those variance floors
for the prime source.
-/
theorem run10bk_rational_resplit_negative_cap_mean
    (u v : ℝ)
    (hu : (1 / 91 : ℝ) ^ 2 ≤ u)
    (hv : (4999 / 5000 : ℝ) ^ 2 ≤ v) :
    (2021 / 2000 : ℝ) *
        run10bkMass u v (1 / 91 : ℝ) (4999 / 5000 : ℝ) -
      run10bkTilt u v (1 / 91 : ℝ) (4999 / 5000 : ℝ) < 0 := by
  have hc : (0 : ℝ) ≤ (1 / 91 : ℝ) := by norm_num
  have hd : (0 : ℝ) ≤ (4999 / 5000 : ℝ) := by norm_num
  have htilt := run10bk_shift_sum_mass_le_tilt
    u v (1 / 91 : ℝ) (4999 / 5000 : ℝ) hc hd hu hv
  have hgap :
      (2021 / 2000 : ℝ) < (1 / 91 : ℝ) + (4999 / 5000 : ℝ) := by
    norm_num
  have hc2 : (0 : ℝ) < (1 / 91 : ℝ) ^ 2 := by norm_num
  have hd2 : (0 : ℝ) < (4999 / 5000 : ℝ) ^ 2 := by norm_num
  have hcu : 0 < (1 / 91 : ℝ) ^ 2 + u := by
    nlinarith
  have hdv : 0 < (4999 / 5000 : ℝ) ^ 2 + v := by
    nlinarith
  have hmass :
      0 < run10bkMass u v (1 / 91 : ℝ) (4999 / 5000 : ℝ) := by
    unfold run10bkMass
    exact mul_pos hcu hdv
  nlinarith

#check run10bkMass
#check run10bkTilt
#check run10bk_lower_tilt_identity
#print axioms run10bk_lower_tilt_identity
#check run10bk_shift_sum_mass_le_tilt
#print axioms run10bk_shift_sum_mass_le_tilt
#check run10bk_rational_resplit_margins
#print axioms run10bk_rational_resplit_margins
#check run10bk_rational_resplit_negative_cap_mean
#print axioms run10bk_rational_resplit_negative_cap_mean

end Millennium.RH
