import Mathlib

/-!
# PNP optimal repetition-sketch finite firewalls

This file formalizes only finite scalar and finite-sum consequences used in the
round-42 RepSAT audit. It does not formalize probability spaces, Fourier
analysis on `F_2^2`, Boolean circuits, repetition codes, SAT, NP, or `P ≠ NP`.
-/

namespace MillenniumBraid
namespace B2Round42PNP

/-- The exact four-symbol column distribution used by the fixed rational
instance sums to one. -/
theorem fixed_column_distribution_sum :
    (13 : ℝ) / 40 + (1 : ℝ) / 3 + (1 : ℝ) / 3 + (1 : ℝ) / 120 = 1 := by
  norm_num

/-- The expected total number of row incidences contributed by one column is
`41/60`. -/
theorem fixed_expected_column_weight :
    (1 : ℝ) / 3 + (1 : ℝ) / 3 + 2 * ((1 : ℝ) / 120) = (41 : ℝ) / 60 := by
  norm_num

/-- The second moment of the one-column support weight is `7/10`. -/
theorem fixed_column_second_moment :
    (1 : ℝ) / 3 + (1 : ℝ) / 3 + 4 * ((1 : ℝ) / 120) = (7 : ℝ) / 10 := by
  norm_num

/-- The exact one-column support variance. -/
theorem fixed_column_variance :
    (7 : ℝ) / 10 - ((41 : ℝ) / 60) ^ 2 = (839 : ℝ) / 3600 := by
  norm_num

/-- The exact variance is strictly below `1/4`, enabling the `4*sqrt(d)`
Chebyshev cap used in the prose theorem. -/
theorem fixed_column_variance_lt_quarter :
    (839 : ℝ) / 3600 < (1 : ℝ) / 4 := by
  norm_num

/-- The raw miss probability on a weight-two syndrome for the fixed rational
column distribution. -/
theorem fixed_weight_two_raw_miss :
    ((13 : ℝ) / 40) ^ 2
      + 2 * ((1 : ℝ) / 3) ^ 2
      + ((1 : ℝ) / 120) ^ 2
      = (787 : ℝ) / 2400 := by
  norm_num

/-- Conditioning on an event of probability at least `63/64` still leaves the
fixed weight-two error strictly below `1/3`. -/
theorem fixed_conditioned_error_below_third :
    ((787 : ℝ) / 2400) / ((63 : ℝ) / 64) < (1 : ℝ) / 3 := by
  norm_num

/-- The exact positive margin in the preceding conditioned-error calculation. -/
theorem fixed_conditioned_error_margin :
    (1 : ℝ) / 3 - ((787 : ℝ) / 2400) / ((63 : ℝ) / 64)
      = (1 : ℝ) / 4725 := by
  norm_num

/-- The two-bit Fourier miss profile used in the human proof. -/
noncomputable def missProfile (η : ℝ) (w : ℕ) : ℝ :=
  (1 + 2 * ((1 : ℝ) / 3 - 2 * η) ^ w + (-(1 : ℝ) / 3) ^ w) / 4

/-- Exact weight-one miss probability. -/
theorem missProfile_one (η : ℝ) :
    missProfile η 1 = (1 : ℝ) / 3 - η := by
  unfold missProfile
  ring

/-- Exact weight-two miss probability. -/
theorem missProfile_two (η : ℝ) :
    missProfile η 2 = (1 : ℝ) / 3 - (2 : ℝ) / 3 * η + 2 * η ^ 2 := by
  unfold missProfile
  ring

/-- For `0 < η < 1/3`, the weight-two raw miss is strictly below `1/3`. -/
theorem missProfile_two_lt_third
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < (1 : ℝ) / 3) :
    missProfile η 2 < (1 : ℝ) / 3 := by
  rw [missProfile_two]
  nlinarith [mul_pos hη0 (sub_pos.mpr hη1)]

/-- Weight two is strictly worse than weight one for every positive `η`. -/
theorem weight_two_exceeds_weight_one
    {η : ℝ} (hη : 0 < η) :
    missProfile η 1 < missProfile η 2 := by
  rw [missProfile_one, missProfile_two]
  nlinarith [sq_nonneg η]

/-- Scalar form of the unit-column lower bound: if total hit mass is at least
`2d/3`, expected support dominates hit mass, and the worst-case cap dominates
expected support, then the cap is at least `2d/3`. -/
theorem unit_column_support_lower_bound
    {d hitMass expectedSupport cap : ℝ}
    (hhit : (2 : ℝ) / 3 * d ≤ hitMass)
    (hdom : hitMass ≤ expectedSupport)
    (hcap : expectedSupport ≤ cap) :
    (2 : ℝ) / 3 * d ≤ cap := by
  linarith

/-- Finite-sum form of the same lower bound. -/
theorem finite_unit_column_support_lower_bound
    {ι : Type*} [Fintype ι]
    (hit expectedWeight : ι → ℝ) (cap : ℝ)
    (hhit : ∀ i, (2 : ℝ) / 3 ≤ hit i)
    (hdom : ∀ i, hit i ≤ expectedWeight i)
    (hcap : ∑ i, expectedWeight i ≤ cap) :
    ∑ _i : ι, ((2 : ℝ) / 3) ≤ cap := by
  calc
    ∑ _i : ι, ((2 : ℝ) / 3) ≤ ∑ i, hit i := by
      exact Finset.sum_le_sum (fun i _hi => hhit i)
    _ ≤ ∑ i, expectedWeight i := by
      exact Finset.sum_le_sum (fun i _hi => hdom i)
    _ ≤ cap := hcap

/-- Exact gate-budget regrouping after writing `N=d+m`. -/
theorem repSAT_gate_budget_regroup
    (s d m tail : ℝ) :
    s + ((2 : ℝ) / 3 * d + tail) + 2 * m + 2
      = (2 : ℝ) / 3 * (d + m) + s + (4 : ℝ) / 3 * m + tail + 2 := by
  ring

/-- The fixed rational support coefficient `41/60` is only `1/60` above the
unit-column information lower bound `2/3`. -/
theorem fixed_coefficient_gap :
    (41 : ℝ) / 60 - (2 : ℝ) / 3 = (1 : ℝ) / 60 := by
  norm_num

#print axioms fixed_column_distribution_sum
#print axioms fixed_expected_column_weight
#print axioms fixed_column_second_moment
#print axioms fixed_column_variance
#print axioms fixed_column_variance_lt_quarter
#print axioms fixed_weight_two_raw_miss
#print axioms fixed_conditioned_error_below_third
#print axioms fixed_conditioned_error_margin
#print axioms missProfile_one
#print axioms missProfile_two
#print axioms missProfile_two_lt_third
#print axioms weight_two_exceeds_weight_one
#print axioms unit_column_support_lower_bound
#print axioms finite_unit_column_support_lower_bound
#print axioms repSAT_gate_budget_regroup
#print axioms fixed_coefficient_gap

end B2Round42PNP
end MillenniumBraid
