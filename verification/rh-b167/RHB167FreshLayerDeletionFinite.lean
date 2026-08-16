import Mathlib

/-!
# RH B167 fresh-layer deletion finite core

Finite real algebra only.  This file formalizes the load-bearing deterministic
inequalities behind the B167 reduction of the B165/B166 cell kernel:

* the fresh-cell geometric numerator bound;
* the distance-to-endpoint square bound;
* conversion of a pointwise coefficient ceiling plus a count ceiling into the
  cubic total fresh-layer budget;
* deletion of a nonnegative fresh layer under a paid tolerance;
* the reverse monotonicity step showing that a frozen-prefix lower bound also
  bounds the full cell.

It does **not** formalize primes, prime counting, BMS/B157/B165, integrals,
Mellin theory, zeta, BGST, the B46 explicit formula, or RH.
-/

namespace RHB167FreshLayerDeletionFinite

/-- On a short root cell `a <= t` and `b <= 2a`, the factor multiplying the
quadratic distance in the B166 fresh-prime kernel satisfies the elementary
cross-multiplied bound `a (b+2t) <= 4 t^2`. -/
theorem fresh_ratio_cross_bound
    {a b t : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (hba : b ≤ 2 * a) :
    a * (b + 2 * t) ≤ 4 * t ^ 2 := by
  have ht0 : 0 ≤ t := le_trans (le_of_lt ha) hat
  have hbt : b ≤ 2 * t := by linarith
  have hsum : b + 2 * t ≤ 4 * t := by linarith
  have ha0 : 0 ≤ a := le_of_lt ha
  have hmul1 : a * (b + 2 * t) ≤ a * (4 * t) :=
    mul_le_mul_of_nonneg_left hsum ha0
  have h4t0 : 0 ≤ 4 * t := by nlinarith
  have hmul2 : a * (4 * t) ≤ t * (4 * t) :=
    mul_le_mul_of_nonneg_right hat h4t0
  calc
    a * (b + 2 * t) ≤ a * (4 * t) := hmul1
    _ ≤ t * (4 * t) := hmul2
    _ = 4 * t ^ 2 := by ring

/-- If `a <= t <= b`, then the fresh-prime distance to the right endpoint is
bounded by the full cell width. -/
theorem endpoint_square_le_cell_square
    {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    (b - t) ^ 2 ≤ (b - a) ^ 2 := by
  have h1 : 0 ≤ b - t := sub_nonneg.mpr htb
  have h2 : b - t ≤ b - a := by linarith
  nlinarith

/-- Abstract scalar version of the B167 fresh-layer counting argument.  If at
most `3 a h` objects occur and every nonnegative coefficient is at most
`4 h^2/(3a)`, then their total contribution is at most `4 h^3`. -/
theorem cubic_budget_from_count_and_coefficient
    {a h count coeff fresh : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h)
    (hcount : count ≤ 3 * a * h)
    (hcoeff0 : 0 ≤ coeff) (hcoeff : coeff ≤ 4 * h ^ 2 / (3 * a))
    (hfresh : fresh ≤ count * coeff) :
    fresh ≤ 4 * h ^ 3 := by
  have hcap0 : 0 ≤ 3 * a * h := by positivity
  calc
    fresh ≤ count * coeff := hfresh
    _ ≤ (3 * a * h) * coeff :=
      mul_le_mul_of_nonneg_right hcount hcoeff0
    _ ≤ (3 * a * h) * (4 * h ^ 2 / (3 * a)) :=
      mul_le_mul_of_nonneg_left hcoeff hcap0
    _ = 4 * h ^ 3 := by
      field_simp [ne_of_gt ha]
      <;> ring

/-- Forward deletion step.  If the full normalized cell is nonnegative, the
fresh layer costs at most `4 h^3`, and the tolerance can pay `4 h^2`, then the
frozen normalized cell is above the same tolerance floor. -/
theorem full_nonnegative_forces_frozen_floor
    {a h T frozen fresh : ℝ}
    (hh : 0 < h)
    (hfresh : fresh ≤ 4 * h ^ 3)
    (hpay : 4 * h ^ 2 ≤ a * T)
    (hfull : 0 ≤ frozen + fresh / h) :
    -a * T ≤ frozen := by
  have hnorm : fresh / h ≤ 4 * h ^ 2 := by
    apply (div_le_iff₀ hh).2
    nlinarith
  linarith

/-- Reverse monotonicity step.  A lower bound for the frozen normalized cell
immediately transfers to the full cell after adding any nonnegative fresh layer. -/
theorem frozen_floor_transfers_to_full
    {a h T frozen fresh : ℝ}
    (hh : 0 < h) (hfresh0 : 0 ≤ fresh)
    (hfrozen : -a * T ≤ frozen) :
    -a * T ≤ frozen + fresh / h := by
  have hdiv : 0 ≤ fresh / h := div_nonneg hfresh0 (le_of_lt hh)
  linarith

/-- The fresh-layer ceiling alone implies the normalized fresh payment
`fresh/h <= 4 h^2`. -/
theorem normalized_fresh_cubic_ceiling
    {h fresh : ℝ} (hh : 0 < h) (hfresh : fresh ≤ 4 * h ^ 3) :
    fresh / h ≤ 4 * h ^ 2 := by
  exact (div_le_iff₀ hh).2 (by nlinarith)

#print axioms fresh_ratio_cross_bound
#print axioms endpoint_square_le_cell_square
#print axioms cubic_budget_from_count_and_coefficient
#print axioms full_nonnegative_forces_frozen_floor
#print axioms frozen_floor_transfers_to_full
#print axioms normalized_fresh_cubic_ceiling

end RHB167FreshLayerDeletionFinite
